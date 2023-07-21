(* Translation to transition system *)
module Pipit.System.Exp

(*SHELVED: use Pipit.Norm.System
open Pipit.Prim.Table
open Pipit.Exp.Base
module Causal = Pipit.Exp.Causality

module CR = Pipit.Context.Row

open Pipit.System.Base
open Pipit.System.Det


(* A system we get from translating an expression *)
let xsystem (#t: table) (c: context t) (state: Type) (value: Type) = system (row c) state value
(* Same, but deterministic *)
let xdsystem (#t: table) (c: context t) (state: Type) (value: Type) = dsystem (row c) state value

let xsystem_stepn
  (#tbl: table)
  (#c: context tbl)
  (#state #value: Type)
  (t: xsystem c state value)
  (streams: list (row c & value))
  (s': state): prop =
  system_stepn t streams s'

let rec state_of_exp (#t: table) (#c: context t) (e: exp t c 'a): Tot Type (decreases e) =
  match e with
  | XVal v -> unit
  | XPrim p -> unit
  | XBVar x -> unit
  | XVar x -> unit
  | XApp f e -> state_of_exp f & state_of_exp e
  | XFby v e1 -> state_of_exp e1 & 'a
  | XThen e1 e2 -> system_then_state (state_of_exp e1) (state_of_exp e2)
  | XMu e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 & state_of_exp e2
  // Contracts do not expose their body, so we only need state of assumptions, guarantee and arg
  // | XContract assm guar body arg ->
  //   state_of_exp assm &
  //   state_of_exp guar &
  //   state_of_exp arg
  | XCheck name e1 e2 -> (t.ty_sem t.propty & state_of_exp e1) & state_of_exp e2

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

let rec system_of_exp_rel
  (#t: table) (#c: context t)
  (e: exp t c 'a { Causal.causal e }):
    Tot (xsystem c (state_of_exp e) 'a) (decreases e) =
  // if exp_is_function e then system_of_dsystem (dsystem_of_exp e)
  // else
    match e with
    | XVal v -> system_const v
    | XPrim p -> system_const (t.prim_sem p)
    | XBVar x -> system_map (fun i -> CR.index (context_sem c) i x) system_input
    | XVar x -> false_elim ()
    | XApp e1 e2 ->
      assert_norm (Causal.causal (XApp e1 e2) ==> (Causal.causal e1 && Causal.causal e2));
      let t1 = system_of_exp_rel e1 in
      let t2 = system_of_exp_rel e2 in
      let t': xsystem c (state_of_exp (XApp e1 e2)) 'a = system_ap2 t1 t2 in
      t'
    | XFby v e1 ->
      system_pre v (system_of_exp_rel e1)
    | XThen e1 e2 ->
      system_then (system_of_exp_rel e1) (system_of_exp_rel e2)
    | XMu e1 ->
      let t' = system_of_exp_rel e1 in
      system_mu #(row c) #('a & row c) (fun i v -> (v, i)) t'
    | XLet b e1 e2 ->
      system_let (fun i v -> (v, i)) (system_of_exp_rel e1) (system_of_exp_rel e2)
    // | XContract assm guar body arg ->
    //   system_contract_instance (fun i b -> (b, ())) (fun i a b -> (a, (b, ())))
    //     (system_bool_holds (system_of_exp_rel assm))
    //     (system_bool_holds (system_of_exp_rel guar))
    //     (system_of_exp_rel arg)
    | XCheck name e1 e2 ->
      let t1 = system_check t.propty_sem (t.propty_of_bool true) name (system_of_exp_rel e1) in
      let t2 = system_of_exp_rel e2 in
      let t': xsystem c (state_of_exp (XCheck name e1 e2)) 'a = system_let (fun i v -> i) t1 t2 in
      t'

let system_of_exp (#t: table) (#c: context t) (e: exp t c 'a { Causal.causal e }) =
  system_of_dsystem (dsystem_of_exp e)
*)