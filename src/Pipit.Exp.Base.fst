(* Definition of base expression type *)
module Pipit.Exp.Base

open Pipit.Prim.Table

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties

#push-options "--print_implicits --print_universes"
(* Expressions `exp t c a`
  expressions are indexed by the primitive table, the environment mapping
  variable indices to value types, and the result type. The primitive table
  describes the allowed value types and primitive operations. The result type
  is a type at universe 1 and can contain functions (the types of primops) and
  propositions. Handling primitive applications this way
  means that we only have one recursive datatype, rather than mutual recursion
  between this and a list-of-applications, or something. I don't know if it's
  a good idea or not.
*)
noeq
type exp (t: table) (c: context t): Type0 -> Type =
  // v
  //  the type of value must be eqtype
  | XVal   : #valty: t.ty -> v: t.ty_sem valty -> exp t c (t.ty_sem valty)
  // bound variable (de Bruijn index)
  | XBVar  : i: C.index_lookup c -> exp t c (t.ty_sem (C.get_index c i))
  // free variables
  //  the types in the variable must be t.ty (which is eqtype) because we need to compare the types of variables
  | XVar   : #valty: t.ty -> x: C.var valty -> exp t c (t.ty_sem valty)
  // primitives
  | XPrim  : p: t.prim -> exp t c (funty_sem t.ty_sem (t.prim_ty p))
  // f(e,...)
  | XApp   : #arg: Type -> #ret: Type -> exp t c (arg -> ret) -> exp t c arg -> exp t c ret
  // v fby e
  // the type of value must be `eqtype`
  | XFby   : #valty: t.ty -> v: t.ty_sem valty -> exp t c (t.ty_sem valty) -> exp t c (t.ty_sem valty)
  // e -> e'
  //  the type here could be relaxed to anything (!!)
  | XThen  : #valty: t.ty -> exp t c (t.ty_sem valty) -> exp t c (t.ty_sem valty) -> exp t c (t.ty_sem valty)
  // µx. e[x]
  //  do we need default for this?
  | XMu    : #valty: t.ty -> exp t (valty :: c) (t.ty_sem valty) -> exp t c (t.ty_sem valty)
  // let x = e in e[x]
  // XXX relax this from (valty: t.ty) to 'a: this makes it easier to infer `XLet e1 e2`. do we want to do same for XFby and XThen?
  | XLet   : b: t.ty -> exp t c (t.ty_sem b) -> exp t (b :: c) 'a -> exp t c 'a

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
  | XCheck : string -> exp t c (t.ty_sem t.propty) -> exp t c 'a -> exp t c 'a

type val_exp (t: table) (c: context t) (a: t.ty) = exp t c (t.ty_sem a)

let rec weaken (#c c': context 't) (e: exp 't c 'a): Tot (exp 't (C.append c c') 'a) (decreases e) =
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
      let aa = XMu?.valty e in
      let e1': exp 't (C.append (C.lift1 c 0 aa) c') 'a = weaken c' e1 in
      let e1'': exp 't (C.lift1 (C.append c c') 0 aa) 'a = e1' in
      XMu e1''
  | XLet b e1 e2 -> XLet b (weaken c' e1) (weaken c' e2)
  | XCheck name e1 e2 -> XCheck name (weaken c' e1) (weaken c' e2)


let is_base_exp (#c: context 't) (e: exp 't c 'a): bool = match e with
 | XVal _ | XVar _ | XBVar _ | XPrim _ -> true
 | _ -> false

let base_exp (t: table) (c: context t) (a: Type)  = e: exp t c a { is_base_exp e }
