(* Translation to transition system *)
module Pipit.System.Exp

open Pipit.Prim.Table
open Pipit.Exp.Base

module Causal = Pipit.Exp.Causality
module CR = Pipit.Context.Row
module PM = Pipit.Prop.Metadata

open Pipit.System.Base
open Pipit.System.Det


(* A system we get from translating an expression *)
let xsystem (#t: table) (c: context t) (state: Type) (value: Type) = system (row c) state value
(* Same, but deterministic *)
let xdsystem (#t: table) (c: context t) (state: Type) (value: Type) = dsystem (row c) state value
(* A pure function with no streaming *)
let xpure (#t: table) (c: context t) (value: Type) = row c -> value

let xsystem_stepn
  (#tbl: table)
  (#c: context tbl)
  (#state #value: Type)
  (t: xsystem c state value)
  (streams: list (row c & value))
  (s': state): prop =
  system_stepn t streams s'

let rec exp_is_pure (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot bool (decreases e) =
  match e with
  | XBase _ -> true
  | XApps e1 -> exp_apps_is_pure e1
  | XFby v e1 -> false
  | XMu e1 -> false
  | XLet b e1 e2 -> exp_is_pure e1 && exp_is_pure e2
  // Checks are conceptually wrapped in an "always", so we don't treat them as pure
  | XCheck name e1 -> false
  | XContract status rely guar impl ->
    false

and exp_apps_is_pure (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot bool (decreases e) =
  match e with
  | XPrim _ -> true
  | XApp f e -> exp_apps_is_pure f && exp_is_pure e



let rec state_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot Type (decreases e) =
  if exp_is_pure e then unit else
  match e with
  | XBase _ -> unit
  | XApps e1 -> state_of_exp_apps e1
  | XFby v e1 -> state_of_exp e1 & t.ty_sem a
  | XMu e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 & state_of_exp e2
  | XCheck name e1 -> bool & state_of_exp e1
  // Contracts do not expose their body in abstract mode, so we only need state of rely and guar
  | XContract status rely guar impl ->
    (bool & bool) & (state_of_exp rely & state_of_exp guar)

and state_of_exp_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot Type (decreases e) =
  match e with
  | XPrim _ -> unit
  | XApp f e -> state_of_exp e & state_of_exp_apps f

let state_of_contract_definition (#t: table) (#c: context t) (#a: t.ty)
  (rely: exp t c t.propty) (guar: exp t (a :: c) t.propty) (impl: exp t c a): Type =
  (bool & bool) & (state_of_exp rely & (state_of_exp guar & state_of_exp impl))

let rec dstate_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot Type (decreases e) =
  if exp_is_pure e then unit else
  match e with
  | XBase _ -> unit
  | XApps e1 -> dstate_of_exp_apps e1
  | XFby v e1 -> dstate_of_exp e1 & t.ty_sem a
  | XMu e1 -> dstate_of_exp e1
  | XLet b e1 e2 -> dstate_of_exp e1 & dstate_of_exp e2
  | XCheck name e1 -> bool & dstate_of_exp e1
  | XContract status rely guar impl ->
    dstate_of_exp impl

and dstate_of_exp_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot Type (decreases e) =
  match e with
  | XPrim _ -> unit
  | XApp f e -> dstate_of_exp e & dstate_of_exp_apps f


let rec exp_is_deterministic (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot bool (decreases e) =
  match e with
  | XBase _ -> true
  | XApps e1 -> exp_apps_is_deterministic e1
  | XFby v e1 -> exp_is_deterministic e1
  | XMu e1 -> exp_is_deterministic e1
  | XLet b e1 e2 -> exp_is_deterministic e1 && exp_is_deterministic e2
  | XCheck name e1 -> exp_is_deterministic e1
  // To express contracts, we want a relational rather than functional system
  | XContract status rely guar impl ->
    false

and exp_apps_is_deterministic (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot bool (decreases e) =
  match e with
  | XPrim _ -> true
  | XApp f e -> exp_apps_is_deterministic f && exp_is_deterministic e

let lemma_state_dstate_det (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a { exp_is_deterministic e }):
  Lemma (state_of_exp e == dstate_of_exp e) =
  admit ()

let pure_of_exp_base
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp_base t c a { Causal.causal_base e }):
    Tot (xpure c (t.ty_sem a)) (decreases e) =
    match e with
    | XVal v -> (fun _ -> v)
    | XBVar x -> (fun i -> CR.index (context_sem c) i x)
    | XVar x -> false_elim ()

let rec pure_of_exp
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { Causal.causal e /\ exp_is_pure e }):
    Tot (xpure c (t.ty_sem a)) (decreases e) =
    match e with
    | XBase e1 -> pure_of_exp_base e1
    | XApps e1 ->
      let t = pure_of_exp_apps e1 (fun r _ -> r) in
      (fun r -> t () r)
    | XLet b e1 e2 ->
      let t1 = pure_of_exp e1 in
      let t2 = pure_of_exp e2 in
      (fun i -> let v1 = t1 i in t2 (v1, i))
    | XFby _ _ | XMu _ | XCheck _ _ | XContract _ _ _ _ ->
      false_elim ()

and pure_of_exp_apps
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (e: exp_apps t c a { Causal.causal_apps e /\ exp_apps_is_pure e })
  (f: funty_sem t.ty_sem a -> inp -> res):
    Tot (inp -> row c -> res) (decreases e) =
    match e with
    | XPrim p -> (fun i r -> f (t.prim_sem p) i)
    | XApp e1 e2 ->
      let arg = XApp?.arg e in
      let ret = XApp?.ret e in
      lemma_funty_sem_FTFun t.ty_sem arg ret;
      let t1: (t.ty_sem arg & inp) -> row c -> res = pure_of_exp_apps e1 (fun r i -> f (r (fst i)) (snd i)) in
      let t2: xpure c (t.ty_sem arg) = pure_of_exp e2 in
      (fun i r -> t1 (t2 r, i) r)


// let dsystem_of_exp_base
//   (#t: table) (#c: context t) (#a: t.ty)
//   (e: exp_base t c a { Causal.causal_base e }):
//     Tot (xdsystem c unit (t.ty_sem a)) (decreases e) =
//     match e with
//     | XVal v -> dsystem_const v
//     | XBVar x -> dsystem_project (fun i -> CR.index (context_sem c) i x)
//     | XVar x -> false_elim ()


let rec dsystem_of_exp
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { Causal.causal e }):
    Tot (xdsystem c (dstate_of_exp e) (t.ty_sem a)) (decreases e) =
  // PERF:TRANS: See note: translation complexity
  if exp_is_pure e
  then dsystem_project (pure_of_exp e)
  else
    match e with
    | XBase e1 -> false_elim ()
    | XApps e1 ->
      let t: dsystem (unit & row c) (dstate_of_exp_apps e1) (t.ty_sem a) = dsystem_of_exp_apps e1 (fun r i -> r) in
      dsystem_with_input (fun s -> ((), s)) t
    | XFby v e1 ->
      dsystem_pre v (dsystem_of_exp e1)
    | XMu e1 ->
      let t' = dsystem_of_exp e1 in
      dsystem_mu_causal #(row c) #(t.ty_sem a & row c) (t.val_default a) (fun i v -> (v, i)) t'
    | XLet b e1 e2 ->
      dsystem_let (fun i v -> (v, i)) (dsystem_of_exp e1) (dsystem_of_exp e2)
    | XCheck status e1 ->
      dsystem_check "XCheck" status (dsystem_of_exp e1)
    | XContract status rely guar impl ->
      dsystem_of_exp impl

and dsystem_of_exp_apps
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (e: exp_apps t c a { Causal.causal_apps e })
  (f: funty_sem t.ty_sem a -> inp -> res):
    Tot (dsystem (inp & row c) (dstate_of_exp_apps e) res) (decreases e) =
    match e with
    | XPrim p -> dsystem_project  (fun i -> f (t.prim_sem p) (fst i))
    | XApp e1 e2 ->
      let arg = XApp?.arg e in
      let ret = XApp?.ret e in
      lemma_funty_sem_FTFun t.ty_sem arg ret;
      let t1: dsystem ((t.ty_sem arg & inp) & row c) _ res = dsystem_of_exp_apps e1 (fun r i -> f (r (fst i)) (snd i)) in
      let t2: xdsystem c _ (t.ty_sem arg) = dsystem_of_exp e2 in
      let t2': dsystem (inp & row c) _ (t.ty_sem arg) = dsystem_with_input snd t2 in
      dsystem_let (fun i v -> ((v, fst i), snd i)) t2' t1



let rec system_of_exp
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { Causal.causal e }):
    Tot (xsystem c (state_of_exp e) (t.ty_sem a)) (decreases e) =
  // PERF:TRANS: wrong complexity!
  // Note: translation complexity:
  // This has the wrong complexity. We descend into the expression to check if it's deterministic, but each sub-call will also descend.
  // The right way to do this is probably to create a datatype that can represent both xsystem and xdsystem, and have combinators to join them together.
  if exp_is_deterministic e
  then (
    lemma_state_dstate_det e;
    system_of_dsystem (dsystem_of_exp e))
  else
    match e with
    | XBase e1 -> false_elim ()
    | XApps e1 ->
      assume (not (exp_is_pure e));
      let t: system (unit & row c) (state_of_exp_apps e1) (t.ty_sem a) = system_of_exp_apps e1 (fun r i -> r) in
      system_with_input (fun s -> ((), s)) t
    | XFby v e1 ->
      system_pre v (system_of_exp e1)
    | XMu e1 ->
      let t' = system_of_exp e1 in
      system_mu #(row c) #(t.ty_sem a & row c) (fun i v -> (v, i)) t'
    | XLet b e1 e2 ->
      assume (not (exp_is_pure e));
      system_let (fun i v -> (v, i)) (system_of_exp e1) (system_of_exp e2)
    | XCheck status e1 ->
      system_check "XCheck" status (system_of_exp e1)
    | XContract status rely guar impl ->
      let tr = system_of_exp rely in
      let tg = system_of_exp guar in
      system_contract_instance status tr tg

and system_of_exp_apps
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (e: exp_apps t c a { Causal.causal_apps e })
  (f: funty_sem t.ty_sem a -> inp -> res):
    Tot (system (inp & row c) (state_of_exp_apps e) res) (decreases e) =
    match e with
    | XPrim p -> system_project (fun i -> f (t.prim_sem p) (fst i))
    | XApp e1 e2 ->
      let arg = XApp?.arg e in
      let ret = XApp?.ret e in
      lemma_funty_sem_FTFun t.ty_sem arg ret;
      let t1: system ((t.ty_sem arg & inp) & row c) _ res = system_of_exp_apps e1 (fun r i -> f (r (fst i)) (snd i)) in
      let t2: xsystem c _ (t.ty_sem arg) = system_of_exp e2 in
      let t2': system (inp & row c) _ (t.ty_sem arg) = system_with_input snd t2 in
      system_let (fun i v -> ((v, fst i), snd i)) t2' t1

let system_of_contract
  (#t: table) (#c: context t) (#a: t.ty)
  (r: exp t       c  t.propty { Causal.causal r })
  (g: exp t (a :: c) t.propty { Causal.causal g })
  (i: exp t       c         a { Causal.causal i }):
    xsystem c (state_of_contract_definition r g i) (t.ty_sem a) =
  let tr = system_of_exp r in
  let tg = system_of_exp g in
  let ti = system_of_exp i in
  system_contract_definition tr tg ti
