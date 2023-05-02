(* Translation to transition system *)
module Pipit.System.Exp


open Pipit.System.Base
open Pipit.System.Det

open Pipit.Exp.Base
// open Pipit.Exp.Bigstep
// open Pipit.Exp.Causality

module C = Pipit.Context

(* A system we get from translating an expression *)
let xsystem (c: C.context) (state: Type) (value: Type) = system (C.row c) state value
(* Same, but deterministic *)
let xdsystem (c: C.context) (state: Type) (value: Type) = dsystem (C.row c) state value

let xsystem_stepn
  (#c: C.context)
  (#state #value: Type)
  (t: xsystem c state value)
  (streams: list (C.row c & value))
  (s': state): prop =
  system_stepn t streams s'

let rec state_of_exp (e: exp 'c 'a): Tot Type (decreases e) =
  match e with
  | XVal v -> unit
  | XBVar x -> unit
  | XVar x -> unit
  | XApp f e -> state_of_exp f & state_of_exp e
  | XFby v e1 -> state_of_exp e1 & 'a
  | XThen e1 e2 -> system_then_state (state_of_exp e1) (state_of_exp e2)
  | XMu _ e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 & state_of_exp e2
  // Contracts do not expose their body, so we only need state of assume, guarantee and arg
  | XContract assm guar body arg ->
    state_of_exp assm &
    state_of_exp guar &
    state_of_exp arg
  | XCheck name e1 e2 -> (xprop & state_of_exp e1) & state_of_exp e2

let sem_freevars = (#a: Type) -> (x: C.var a) -> a

let rec dsystem_of_exp (e: exp 'c 'a)
    (fv: sem_freevars):
    Tot (option (xdsystem 'c (state_of_exp e) 'a)) (decreases e) =
  match e with
  | XVal v -> Some (dsystem_const v)
  | XBVar x -> Some (dsystem_map (fun i -> C.row_index 'c i x) dsystem_input)
  | XVar x -> Some (dsystem_const (fv x))
  | XApp e1 e2 ->
    (match dsystem_of_exp e1 fv, dsystem_of_exp e2 fv with
     | Some t1, Some t2 ->
       let t': xdsystem 'c (state_of_exp (XApp e1 e2)) 'a = dsystem_ap2 t1 t2 in
       Some t'
     | _ -> None)
  | XFby v e1 ->
    (match dsystem_of_exp e1 fv with
     | Some t -> Some (dsystem_pre v t)
     | _ -> None)
  | XThen e1 e2 ->
    (match dsystem_of_exp e1 fv, dsystem_of_exp e2 fv with
     | Some t1, Some t2 ->
        Some (dsystem_then t1 t2)
     | _ -> None)
  | XLet b e1 e2 ->
    (match dsystem_of_exp e1 fv, dsystem_of_exp e2 fv with
     | Some t1, Some t2 ->
        Some (dsystem_let (fun i v -> (v, i)) t1 t2)
     | _ -> None)
  | XCheck name e1 e2 ->
    (match dsystem_of_exp e1 fv, dsystem_of_exp e2 fv with
     | Some t1, Some t2 ->
        let t1' = dsystem_check name t1 in
        let t': xdsystem 'c (state_of_exp (XCheck name e1 e2)) 'a = dsystem_let (fun i v -> i) t1' t2 in
        Some t'
     | _ -> None)


  | XMu _ e1 ->
    (match dsystem_of_exp e1 fv with
    | Some t1 ->
      let t' = dsystem_mu_causal #(C.row 'c) #('a & C.row 'c) (fun i v -> (v, i)) t1 in
      Some t'
    | _ -> None)
  | XContract assm guar body arg -> None

let rec system_of_exp (e: exp 'c 'a)
    (fv: sem_freevars):
    Tot (xsystem 'c (state_of_exp e) 'a) (decreases e) =
  match dsystem_of_exp e fv with
  | Some d -> system_of_dsystem d
  | None ->
    match e with
    | XVal v -> system_const v
    | XBVar x -> system_map (fun i -> C.row_index 'c i x) system_input
    | XVar x -> system_const (fv x)
    | XApp e1 e2 ->
      let t1 = system_of_exp e1 fv in
      let t2 = system_of_exp e2 fv in
      let t': xsystem 'c (state_of_exp (XApp e1 e2)) 'a = system_ap2 t1 t2 in
      t'
    | XFby v e1 ->
      system_pre v (system_of_exp e1 fv)
    | XThen e1 e2 ->
      system_then (system_of_exp e1 fv) (system_of_exp e2 fv)
    | XMu _ e1 ->
      let t = system_of_exp e1 fv in
      system_mu #(C.row 'c) #('a & C.row 'c) (fun i v -> (v, i)) t
    | XLet b e1 e2 ->
      system_let (fun i v -> (v, i)) (system_of_exp e1 fv) (system_of_exp e2 fv)
    | XContract assm guar body arg ->
      system_contract_instance (fun i b -> (b, ())) (fun i a b -> (a, (b, ())))
        (system_bool_holds (system_of_exp assm fv))
        (system_bool_holds (system_of_exp guar fv))
        (system_of_exp arg fv)
    | XCheck name e1 e2 ->
      let t1 = system_check name (system_of_exp e1 fv) in
      let t2 = system_of_exp e2 fv in
      let t': xsystem 'c (state_of_exp (XCheck name e1 e2)) 'a = system_let (fun i v -> i) t1 t2 in
      t'
