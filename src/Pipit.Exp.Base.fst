(* Definition of base expression type *)
module Pipit.Exp.Base
module C = Pipit.Context
open Pipit.Prim.Table
open Pipit.Inhabited

(* LATER: restrict "properties" to booleans for now to avoid universe stuff *)
type xprop = bool

noeq
type exp (t: table) (c: C.context t.typ): funty t.typ -> Type =
  // v
  | XVal   : a: t.typ -> v: t.typ_sem a -> exp t c (FTVal a)
  // bound variable (de Bruijn index)
  | XBVar  : a: t.typ -> i: C.index { C.opt_index c i == Some (t.typ_sem a) } -> exp t c (FTVal a)
  // free variables
  | XVar   : a: t.typ -> x: C.var a -> exp t c (FTVal a)
  // primitives
  | XPrim  : p: t.prim -> exp t c (t.prim_types p)
  // f(e,...)
  | XApp   : arg: t.typ -> ret: funty t.typ -> exp t c (FTFun arg ret) -> exp t c [] (FTVal arg) -> exp t c ret
  // v fby e
  | XFby   : a: t.typ -> v: a -> exp t c (FTVal a) -> exp t c (FTVal a)
  // e -> e'
  | XThen  : a: t.typ -> exp c (FTVal a) -> exp c (FTVal a) -> exp c (FTVal a)
  // µx. e[x]
  | XMu    : a: t.typ -> exp (a :: c) (FTVal a) -> exp c (FTVal a)
  // let x = e in e[x]
  | XLet   : a: t.typ -> b: t.typ -> exp c (FTVal b) -> exp (b :: c) (FTVal a) -> exp c (FTVal a)

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


let is_base_exp (e: exp 'c 'a): bool = match e with
 | XVal _ | XVar _ | XBVar _ -> true
 | _ -> false

type base_exp (c: C.context) (a: Type) = e : exp c a { is_base_exp e }
