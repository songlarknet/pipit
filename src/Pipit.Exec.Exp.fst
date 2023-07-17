(* Translation from expressions to executable transition systems *)
module Pipit.Exec.Exp

open Pipit.Prim.Table
open Pipit.Exec.Base
open Pipit.Exp.Base

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

let row_cons (#t: table) (#c: context t) (#a: t.ty) (v: t.ty_sem a) (values: row c): row (C.lift1 c 0 a) = (v, values)

let exec_index (#t: table) (c: context t) (ix: C.index_lookup c):
       exec (row c) unit (List.Tot.index (context_sem c) ix) =
  { init = ()
  ; eval = (fun i s -> CR.index (context_sem c) i ix)
  ; update = (fun i s -> ())
  }

(* XXX: the strict_on_arguments annotation makes it hard to prove that
   > state_of_exp (XApp f e) = (state_of_exp f & state_of_exp e)
   which is trivial without it. What's up? *)
// [@@strict_on_arguments [2]]
let rec state_of_exp (#t: table) (#c: context t) (e: exp t c 'a): Tot Type (decreases e) =
  match e with
  | XVal v -> unit
  | XPrim p -> unit
  | XBVar x -> unit
  | XVar x -> unit
  | XApp f e -> state_of_exp f & state_of_exp e
  | XFby v e -> state_of_exp e & 'a
  | XThen e1 e2 -> bool & state_of_exp e2
  | XMu e1 -> state_of_exp e1
  | XLet b e1 e2 -> state_of_exp e1 & state_of_exp e2
  // | XContract assm guar body arg -> unit
  | XCheck p e1 e2 -> state_of_exp e2

let xexec (#t: table) (#c: context t) (e: exp t c 'a) = exec (row c) (state_of_exp e) 'a

let rec extractable (#t: table) (#c: context t) (e: exp t c 'a): Tot prop (decreases e) =
  match e with
  | XVal v -> True
  | XPrim p -> True
  | XBVar i -> True
  | XVar x -> False
  | XApp e1 e2 -> extractable e1 /\ extractable e2
  | XFby v e1 -> extractable e1
  | XThen e1 e2 -> extractable e1 /\ extractable e2
  | XMu e1 ->
    extractable e1
  | XLet b e1 e2 -> extractable e1 /\ extractable e2
  // | XContract assm guar body arg -> False
  | XCheck p e1 e2 -> extractable e2

let extractable_XApp (#t: table) (#c: context t) (e1: exp t c ('b -> 'a)) (e2: exp t c 'b):
  Lemma (requires (extractable (XApp e1 e2)))
        (ensures (extractable e1)) =
        assert_norm (extractable (XApp e1 e2) ==> extractable e1)

[@@strict_on_arguments [2]]
noextract inline_for_extraction
let rec exec_of_exp (#t: table) (#c: context t) (e: exp t c 'a { extractable e }): Tot (xexec e) (decreases e) =
  match e with
  | XVal v -> exec_const _ v
  | XPrim p -> exec_const _ (t.prim_sem p)
  | XBVar i -> exec_index c i
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
  | XMu e1 ->
    exec_mu (t.val_default (XMu?.valty e)) (fun i v -> row_cons v i) (exec_of_exp e1)
  | XLet b e1 e2 ->
    exec_let (fun i v -> row_cons v i) (exec_of_exp e1) (exec_of_exp e2)
  // | XContract assm guar body arg ->
  | XCheck p e1 e2 -> exec_of_exp e2
