(* Definition of base expression type *)
module Pipit.Exp.Base

open Pipit.Prim.Table

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties

(* Expressions `exp t c a`
  expressions are indexed by the primitive table, the environment mapping
  variable indices to value types, and the result type. The primitive table
  describes the allowed value types and primitive operations. The result type
  is a `funty` describing a real value type (`FTVal t`) or a partial primitive
  application (`FTFun arg rest`). Handling primitive applications this way
  means that we only have one recursive datatype, rather than mutual recursion
  between this and a list-of-applications, or something. I don't know if it's
  a good idea or not.
*)
noeq
type exp (t: table) (c: context t): funty t.ty -> Type =
  // v
  | XVal   : #a: t.ty -> v: t.ty_sem a -> exp t c (FTVal a)
  // bound variable (de Bruijn index)
  | XBVar  : i: C.index_lookup c -> exp t c (FTVal (C.get_index c i))
  // free variables
  | XVar   : #a: t.ty -> x: C.var a -> exp t c (FTVal a)
  // primitives
  | XPrim  : p: t.prim -> exp t c (t.prim_ty p)
  // f(e,...)
  | XApp   : #arg: t.ty -> #ret: funty t.ty -> exp t c (FTFun arg ret) -> exp t c (FTVal arg) -> exp t c ret
  // v fby e
  | XFby   : #a: t.ty -> v: t.ty_sem a -> exp t c (FTVal a) -> exp t c (FTVal a)
  // e -> e'
  | XThen  : #a: t.ty -> exp t c (FTVal a) -> exp t c (FTVal a) -> exp t c (FTVal a)
  // µx. e[x]
  | XMu    : #a: t.ty -> exp t (a :: c) (FTVal a) -> exp t c (FTVal a)
  // let x = e in e[x]
  | XLet   : #a: t.ty -> b: t.ty -> exp t c (FTVal b) -> exp t (b :: c) (FTVal a) -> exp t c (FTVal a)

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
  | XCheck : #a: t.ty -> string -> exp t c (FTVal t.propty) -> exp t c (FTVal a) -> exp t c (FTVal a)

let rec weaken (#a: funty ('t).ty) (#c c': context 't) (e: exp 't c a): Tot (exp 't (C.append c c') a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i' ->
    CP.lemma_append_preserves_get_index c c' i';
    XBVar (i' <: C.index_lookup (C.append c c'))
  | XVar x' -> XVar x'
  | XPrim p -> XPrim p
  | XApp f e -> XApp (weaken c' f) (weaken c' e)
  | XFby v e -> XFby v (weaken c' e)
  | XThen e1 e2 -> XThen (weaken c' e1) (weaken c' e2)
  | XMu e1 ->
      let e1': exp 't (C.append (C.lift1 c 0 (FTVal?.t a)) c') a = weaken c' e1 in
      let e1'': exp 't (C.lift1 (C.append c c') 0 (FTVal?.t a)) a = e1' in
      XMu e1''
  | XLet b e1 e2 -> XLet b (weaken c' e1) (weaken c' e2)
  | XCheck name e1 e2 -> XCheck name (weaken c' e1) (weaken c' e2)


let is_base_exp (#c: context 't) (#a: funty ('t).ty) (e: exp 't c a): bool = match e with
 | XVal _ | XVar _ | XBVar _ | XPrim _ -> true
 | _ -> false

let base_exp (t: table) (c: context t) (a: funty t.ty)  = e: exp t c a { is_base_exp e }

let val_exp (t: table) (c: context t) (a: t.ty) = exp t c (FTVal a)
