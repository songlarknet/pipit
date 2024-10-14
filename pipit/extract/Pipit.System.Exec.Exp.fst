(* Translation to executable transition systems *)
module Pipit.System.Exec.Exp

open Pipit.Prim.Table
open Pipit.Exp.Base

module Causal = Pipit.Exp.Causality
module CR = Pipit.Context.Row
module PM = Pipit.Prop.Metadata

open Pipit.System.Base
open Pipit.System.Exec

module SX = Pipit.System.Exp

noextract inline_for_extraction
let rec estate_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot (option Type) (decreases e) =
  match e with
  | XBase _ -> None
  | XApps e1 -> estate_of_exp_apps e1
  | XFby v e1 -> Some (t.ty_sem a) `type_join` estate_of_exp e1
  | XMu e1 -> estate_of_exp e1
  | XLet b e1 e2 -> estate_of_exp e1 `type_join` estate_of_exp e2
  | XCheck name e1 -> None
  | XContract status rely guar impl ->
    estate_of_exp impl

and estate_of_exp_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot (option Type) (decreases e) =
  match e with
  | XPrim _ -> None
  | XApp f e -> estate_of_exp e `type_join` estate_of_exp_apps f

(* An executable system we get from translating an expression *)
let exsystem (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a) = esystem (row c) (estate_of_exp e) (t.ty_sem a)


noextract inline_for_extraction
let esystem_of_exp_base
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp_base t c a { Causal.causal_base e }):
    Tot (exsystem (XBase e)) (decreases e) =
    match e with
    | XVal v -> esystem_const v
    | XBVar x -> esystem_project (fun i -> CR.index (context_sem c) i x)
    | XVar x -> false_elim ()

noextract inline_for_extraction
let rec esystem_of_exp
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { Causal.causal e }):
    Tot (exsystem e) (decreases e) =
    match e with
    | XBase e1 -> esystem_of_exp_base e1
    | XApps e1 ->
      let t: esystem (unit & row c) (estate_of_exp_apps e1) (t.ty_sem a) = esystem_of_exp_apps e1 SX.system_of_exp_apps_const in
      esystem_with_input (fun s -> ((), s)) t
    | XFby v e1 ->
      esystem_pre v (esystem_of_exp e1)
    | XMu e1 ->
      let t' = esystem_of_exp e1 in
      esystem_mu_causal #(row c) #(t.ty_sem a & row c) (t.val_default a) (fun i v -> (v, i)) t'
    | XLet b e1 e2 ->
      // Tiny optimisation: mark interesting lets as no-inline; variables and values can be inlined
      (match e1 with
      | XBase _ -> esystem_let (fun i v -> (v, i)) (esystem_of_exp e1) (esystem_of_exp e2)
      | _ -> esystem_let_no_inline (fun i v -> (v, i)) (esystem_of_exp e1) (esystem_of_exp e2))
    | XCheck status e1 ->
      esystem_const ()
    | XContract status rely guar impl ->
      esystem_of_exp impl

and
esystem_of_exp_apps
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (e: exp_apps t c a { Causal.causal_apps e })
  (f: funty_sem t.ty_sem a -> inp -> res):
    Tot (esystem (inp & row c) (estate_of_exp_apps e) res) (decreases e) =
    match e with
    | XPrim p -> esystem_project  (fun i -> f (t.prim_sem p) (fst i))
    | XApp e1 e2 ->
      let arg = XApp?.arg e in
      let ret = XApp?.ret e in
      lemma_funty_sem_FTFun t.ty_sem arg ret;
      let t1: esystem ((t.ty_sem arg & inp) & row c) _ res = esystem_of_exp_apps e1 (SX.system_of_exp_apps_distr f) in
      let t2: esystem (row c) _ (t.ty_sem arg) = esystem_of_exp e2 in
      let t2': esystem (inp & row c) _ (t.ty_sem arg) = esystem_with_input snd t2 in
      esystem_let (fun i v -> ((v, fst i), snd i)) t2' t1
