(* Definition of base expression type *)
module Pipit.Exp.Base
module C = Pipit.Context
open Pipit.Inhabited

(* LATER: restrict "properties" to booleans for now to avoid universe stuff *)
type xprop = bool

noeq
type exp (c: C.context) 'a =
  // v
  | XVal   : 'a -> exp c 'a
  // bound variable (de Bruijn index)
  | XBVar  : (i: C.index { C.opt_index c i == Some 'a }) -> exp c 'a
  // free variables
  | XVar   : (x: C.var 'a) -> exp c 'a
  // f(e,...)
  | XApp   : exp c ('b -> 'a) -> exp c 'b -> exp c 'a
  // v fby e
  | XFby   : 'a -> exp c 'a -> exp c 'a
  // e -> e'
  | XThen  : exp c 'a -> exp c 'a -> exp c 'a
  // µx. e[x]
  | XMu    : {| inhabited 'a |} -> exp ('a :: c) 'a -> exp c 'a
  // let x = e in e[x]
  | XLet   : (b: Type) -> exp c b -> exp (b :: c) 'a -> exp c 'a

  // Proof terms
  // Contracts for hiding implementation:
  //   (λx. { assumptions } body { λr. guarantees })(arg)
  // LATER: assumptions and guarantees should probably be in context c, so they can be CSEd with the main expression. body should be separate to allow separate codegen
  // | XContract:
  //          (assumptions: exp ['b] xprop) ->
  //          (guarantees: exp ['a; 'b] xprop) ->
  //          (body: exp ['b] 'a) ->
  //          (arg: exp c 'b) ->
  //          exp c 'a

  // check "" e
  | XCheck : string -> exp c xprop -> exp c 'a -> exp c 'a

let rec weaken (#c c': C.context) (e: exp c 'a): Tot (exp (C.append c c') 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i' ->
    C.lemma_append_preserves_opt_index c c' i';
    XBVar i'
  | XVar x' -> XVar x'
  | XApp f e -> XApp (weaken c' f) (weaken c' e)
  | XFby v e -> XFby v (weaken c' e)
  | XThen e1 e2 -> XThen (weaken c' e1) (weaken c' e2)
  | XMu _ e1 ->
    let e1': exp (C.append (C.lift1 c 0 'a) c') 'a = weaken c' e1 in
    let e1'': exp (C.lift1 (C.append c c') 0 'a) 'a = e1' in
    XMu e1''
  | XLet b e1 e2 -> XLet b (weaken c' e1) (weaken c' e2)
  | XCheck name e1 e2 -> XCheck name (weaken c' e1) (weaken c' e2)
