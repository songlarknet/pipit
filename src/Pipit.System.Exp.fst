(* Translation to transition system *)
module Pipit.System.Exp

open Pipit.Prim.Table
open Pipit.Exp.Base
module Causal = Pipit.Exp.Causality

module CR = Pipit.Context.Row

open Pipit.System.Base
open Pipit.System.Det


(* A system we get from translating an expression *)
let xsystem (#t: table) (c: context t) (state: Type) (value: Type) = system (row c) state value
(* Same, but deterministic *)
// let xdsystem (#t: table) (c: context t) (state: Type) (value: Type) = dsystem (row c) state value

let xsystem_stepn
  (#tbl: table)
  (#c: context tbl)
  (#state #value: Type)
  (t: xsystem c state value)
  (streams: list (row c & value))
  (s': state): prop =
  system_stepn t streams s'

let rec state_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot Type (decreases e) =
  match e with
  | XBase _ -> unit
  | XApps e1 -> state_of_exp_apps e1
  | XFby v e1 -> state_of_exp e1 & t.ty_sem a
  | XMu e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 & state_of_exp e2
  | XCheck name e1 -> (t.ty_sem t.propty & state_of_exp e1)
  // Contracts do not expose their body in abstract mode, so we only need state of rely and guar
  | XContract rely guar impl ->
    state_of_exp rely & state_of_exp guar

and state_of_exp_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot Type (decreases e) =
  match e with
  | XPrim _ -> unit
  | XApp f e -> state_of_exp_apps f & state_of_exp e

let rec system_of_exp
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { Causal.causal e }):
    Tot (xsystem c (state_of_exp e) (t.ty_sem a)) (decreases e) =
  // if exp_is_function e then system_of_dsystem (dsystem_of_exp e)
  // else
    match e with
    | XBase (XVal v) -> system_const v
    | XBase (XBVar x) -> system_map (fun i -> CR.index (context_sem c) i x) system_input
    | XBase (XVar x) -> false_elim ()
    | XApps e1 -> system_of_exp_apps e1
    | XFby v e1 ->
      system_pre v (system_of_exp e1)
    | XMu e1 ->
      let t' = system_of_exp e1 in
      system_mu #(row c) #(t.ty_sem a & row c) (fun i v -> (v, i)) t'
    | XLet b e1 e2 ->
      system_let (fun i v -> (v, i)) (system_of_exp e1) (system_of_exp e2)
    // | XContract assm guar body arg ->
    //   system_contract_instance (fun i b -> (b, ())) (fun i a b -> (a, (b, ())))
    //     (system_bool_holds (system_of_exp assm))
    //     (system_bool_holds (system_of_exp guar))
    //     (system_of_exp arg)
    | XCheck name e1 ->
      system_check t.propty_sem (t.propty_of_bool true) name (system_of_exp e1)
    | XContract rely guar impl ->
      admit ()

and system_of_exp_apps
  (#t: table) (#c: context t) (#a: funty t.ty)
  (e: exp_apps t c a { Causal.causal_apps e }):
    Tot (xsystem c (state_of_exp_apps e) (funty_sem t.ty_sem a)) (decreases e) =
  // if exp_is_function e then system_of_dsystem (dsystem_of_exp e)
  // else
    match e with
    | XPrim p -> system_const (t.prim_sem p)
    | XApp e1 e2 ->
      let arg = XApp?.arg e in
      let ret = XApp?.ret e in
      lemma_funty_sem_FTFun t.ty_sem (XApp?.arg e) (XApp?.ret e);
      // assert_norm (Causal.causal_ (XApp e1 e2) ==> (Causal.causal e1 && Causal.causal e2));
      let t1: xsystem c _ (funty_sem t.ty_sem (FTFun arg ret)) = system_of_exp_apps e1 in
      let t2: xsystem c _ (t.ty_sem arg) = system_of_exp e2 in
      system_ap2 t1 t2
      // let t': xsystem c (state_of_exp_apps (XApp e1 e2)) (funty_sem t.ty_sem a) = system_ap2 t1 t2 in


(*
let rec dsystem_of_exp (#t: table) (#c: context t) (e: exp t c 'a { Causal.causal e }):
    Tot (xdsystem c (state_of_exp e) 'a) (decreases e) =
  match e with
  | XVal v -> dsystem_const v
  | XPrim p -> dsystem_const (t.prim_sem p)
  | XBVar x -> dsystem_map (fun i -> CR.index (context_sem c) i x) dsystem_input
  | XVar x -> false_elim ()
  | XApp e1 e2 ->
    assert_norm (Causal.causal (XApp e1 e2) ==> (Causal.causal e1 && Causal.causal e2));
    let t1 = dsystem_of_exp e1 in
    let t2 = dsystem_of_exp e2 in
    let t': xdsystem c (state_of_exp (XApp e1 e2)) 'a = dsystem_ap2 t1 t2 in
    t'
  | XFby v e1 ->
    dsystem_pre v (dsystem_of_exp e1)
  | XThen e1 e2 ->
    dsystem_then (dsystem_of_exp e1) (dsystem_of_exp e2)
  | XMu e1 ->
    let t' = dsystem_of_exp e1 in
    dsystem_mu_causal #(row c) #('a & row c) (t.val_default (XMu?.valty e)) (fun i v -> (v, i)) t'
  | XLet b e1 e2 ->
    dsystem_let (fun i v -> (v, i)) (dsystem_of_exp e1) (dsystem_of_exp e2)
  | XCheck name e1 e2 ->
    let t1 = dsystem_check t.propty_sem (t.propty_of_bool true) name (dsystem_of_exp e1) in
    let t2 = dsystem_of_exp e2 in
    let t': xdsystem c (state_of_exp (XCheck name e1 e2)) 'a = dsystem_let (fun i v -> i) t1 t2 in
    t'
*)
