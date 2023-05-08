(* Translation from expressions to executable transition systems *)
module Pipit.Exec.Exp

open Pipit.Exec.Base
open Pipit.Exp.Base
open Pipit.Inhabited

module C = Pipit.Context

let row_cons (#c: C.context) (v: 'a) (values: C.row c): C.row (C.lift1 c 0 'a) = (v, values)

let exec_index (c: C.context) (ix: C.index { C.has_index c ix }):
       exec (C.row c) unit (List.Tot.index c ix) =
  { init = ()
  ; eval = (fun i s -> C.row_index c i ix)
  ; update = (fun i s -> ())
  }

let rec state_of_exp (e: exp 'c 'a): Tot Type (decreases e) =
  match e with
  | XVal v -> unit
  | XBVar x -> unit
  | XVar x -> unit
  | XApp f e -> state_of_exp f & state_of_exp e
  | XFby v e -> state_of_exp e & 'a
  | XThen e1 e2 -> bool & state_of_exp e2
  | XMu _ e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 & state_of_exp e2
  // | XContract assm guar body arg -> unit
  | XCheck p e1 e2 -> state_of_exp e2

let xexec (e: exp 'c 'a) = exec (C.row 'c) (state_of_exp e) 'a

let rec extractable (e: exp 'c 'a): Tot prop (decreases e) =
  match e with
  | XVal v -> True
  | XBVar i -> True
  | XVar x -> False
  | XApp e1 e2 -> extractable e1 /\ extractable e2
  | XFby v e1 -> extractable e1
  | XThen e1 e2 -> extractable e1 /\ extractable e2
  | XMu _ e1 ->
    extractable e1
  | XLet b e1 e2 -> extractable e1 /\ extractable e2
  // | XContract assm guar body arg -> False
  | XCheck p e1 e2 -> extractable e2

let extractable_XApp (e1: exp 'c ('b -> 'a)) (e2: exp 'c 'b):
  Lemma (requires (extractable (XApp e1 e2)))
        (ensures (extractable e1)) =
        assert_norm (extractable (XApp e1 e2) ==> extractable e1)

noextract inline_for_extraction
let rec exec_of_exp (e: exp 'c 'a { extractable e }): Tot (xexec e) (decreases e) =
  match e with
  | XVal v -> exec_const _ v
  | XBVar i -> exec_index 'c i
  // | XVar x ->
  | XApp e1 e2 ->
    extractable_XApp e1 e2;
    let t1 = exec_of_exp e1 in
    let t2 = exec_of_exp e2 in
    let t': xexec (XApp e1 e2) = exec_ap2 t1 t2 in
    t'
  | XFby v e1 ->
    exec_pre v (exec_of_exp e1)
  | XThen e1 e2 ->
    exec_then (exec_of_exp e1) (exec_of_exp e2)
  | XMu i e1 ->
    exec_mu i.get_inhabited (fun i v -> row_cons v i) (exec_of_exp e1)
  | XLet b e1 e2 ->
    exec_let (fun i v -> row_cons v i) (exec_of_exp e1) (exec_of_exp e2)
  // | XContract assm guar body arg ->
  | XCheck p e1 e2 -> exec_of_exp e2
