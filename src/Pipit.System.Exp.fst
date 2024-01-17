(* Translation to transition system *)
module Pipit.System.Exp

open Pipit.Prim.Table
open Pipit.Exp.Base

module Causal = Pipit.Exp.Causality
module CR = Pipit.Context.Row
module PM = Pipit.Prop.Metadata

open Pipit.System.Base


let rec state_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot (option Type) (decreases e) =
  match e with
  | XBase _ -> None
  | XApps e1 -> state_of_exp_apps e1
  | XFby v e1 -> Some (t.ty_sem a) `type_join` state_of_exp e1
  | XMu e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 `type_join` state_of_exp e2
  | XCheck name e1 -> state_of_exp e1
  // Contracts do not expose their body in abstract mode, so we only need state of rely and guar
  | XContract status rely guar impl ->
    state_of_exp rely `type_join` state_of_exp guar

and state_of_exp_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot (option Type) (decreases e) =
  match e with
  | XPrim _ -> None
  | XApp f e -> state_of_exp e `type_join` state_of_exp_apps f

let state_of_contract_definition (#t: table) (#c: context t) (#a: t.ty)
  (rely: exp t c t.propty) (guar: exp t (a :: c) t.propty) (impl: exp t c a): option Type =
  (state_of_exp rely `type_join` (state_of_exp guar `type_join` state_of_exp impl))


let rec oracle_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot (option Type) (decreases e) =
  match e with
  | XBase _ -> None
  | XApps e1 -> oracle_of_exp_apps e1
  | XFby v e1 -> oracle_of_exp e1
  | XMu e1 -> Some (t.ty_sem a) `type_join` oracle_of_exp e1
  | XLet b e1 e2 -> oracle_of_exp e1 `type_join` oracle_of_exp e2
  | XCheck name e1 -> oracle_of_exp e1
  // Contracts do not expose their body in abstract mode, so we only need state of rely and guar
  | XContract status rely guar impl ->
    Some (t.ty_sem a) `type_join` (oracle_of_exp rely `type_join` oracle_of_exp guar)

and oracle_of_exp_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot (option Type) (decreases e) =
  match e with
  | XPrim _ -> None
  | XApp f e -> oracle_of_exp e `type_join` oracle_of_exp_apps f

let oracle_of_contract_definition (#t: table) (#c: context t) (#a: t.ty)
  (rely: exp t c t.propty) (guar: exp t (a :: c) t.propty) (impl: exp t c a): option Type =
  (oracle_of_exp rely `type_join` (oracle_of_exp guar `type_join` oracle_of_exp impl))

(* A system we get from translating an expression *)
let xsystem (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a) = system (row c) (oracle_of_exp e) (state_of_exp e) (t.ty_sem a)

let system_of_exp_base
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp_base t c a):
    Tot (xsystem (XBase e)) (decreases e) =
    match e with
    | XVal v -> system_const v
    | XBVar x -> system_project (fun i -> CR.index (context_sem c) i x)
    (** TODO: use an arbitrary value for free variables. This should be
      * changed to use an explicit oracle variable, or maybe invent a (ghost?)
      * variable of type
      * > free_var: (t: Type) -> time -> var -> t
      *
      * This assumption doesn't affect the soundness of the proof-of-translation
      * as the proof only applies to causal expressions, which do not have free
      * variables.
      **)
    | XVar x -> system_const (t.val_default a)

let system_of_exp_apps_distr
    (#t: table) (#arg: t.ty) (#resfun: funty t.ty) (#res #inp: Type0)
    (f: funty_sem t.ty_sem resfun -> inp -> res)
    (r: funty_sem t.ty_sem (FTFun arg resfun))
    (i: t.ty_sem arg & inp)
  : res =
  f (r (fst i)) (snd i)

let system_of_exp_apps_const (#r #i: Type0)
  (vr: r) (vi: i): r = vr

let rec system_of_exp
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a):
    Tot (xsystem e) (decreases e) =
    match e with
    | XBase e1 -> system_of_exp_base e1
    | XApps e1 ->
      let t: system (unit & row c) (oracle_of_exp_apps e1) (state_of_exp_apps e1) (t.ty_sem a) = system_of_exp_apps e1 system_of_exp_apps_const in
      system_with_input (fun s -> ((), s)) t
    | XFby v e1 ->
      system_pre v (system_of_exp e1)
    | XMu e1 ->
      let t' = system_of_exp e1 in
      system_mu #(row c) #(t.ty_sem a & row c) (fun i v -> (v, i)) t'
    | XLet b e1 e2 ->
      system_let (fun i v -> (v, i)) (system_of_exp e1) (system_of_exp e2)
    | XCheck status e1 ->
      system_check "XCheck" status (system_of_exp e1)
    | XContract status rely guar impl ->
      let tr = system_of_exp rely in
      let tg = system_of_exp guar in
      system_contract_instance status tr tg

and system_of_exp_apps
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (e: exp_apps t c a)
  (f: funty_sem t.ty_sem a -> inp -> res):
    Tot (system (inp & row c) (oracle_of_exp_apps e) (state_of_exp_apps e) res) (decreases e) =
    match e with
    | XPrim p -> system_project (fun i -> f (t.prim_sem p) (fst i))
    | XApp e1 e2 ->
      let arg = XApp?.arg e in
      let ret = XApp?.ret e in
      lemma_funty_sem_FTFun t.ty_sem arg ret;
      let t1: system ((t.ty_sem arg & inp) & row c) _ _ res = system_of_exp_apps e1 (system_of_exp_apps_distr f) in
      let t2: system (row c) _ _ (t.ty_sem arg) = system_of_exp e2 in
      let t2': system (inp & row c) _ _ (t.ty_sem arg) = system_with_input snd t2 in
      system_let (fun i v -> ((v, fst i), snd i)) t2' t1

let system_of_contract
  (#t: table) (#c: context t) (#a: t.ty)
  (r: exp t       c  t.propty)
  (g: exp t (a :: c) t.propty)
  (i: exp t       c         a):
    system (row c) (oracle_of_contract_definition r g i) (state_of_contract_definition r g i) (t.ty_sem a) =
  let tr = system_of_exp r in
  let tg = system_of_exp g in
  let ti = system_of_exp i in
  system_contract_definition tr tg ti
