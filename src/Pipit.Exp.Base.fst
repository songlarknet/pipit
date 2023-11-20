(* Definition of base expression type *)
module Pipit.Exp.Base

open Pipit.Prim.Table

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties
module PM = Pipit.Prop.Metadata

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
type exp_base (t: table) (c: context t): t.ty -> Type =
  // v
  //  the type of value must be eqtype
  | XVal   : #valty: t.ty -> v: t.ty_sem valty -> exp_base t c valty
  // bound variable (de Bruijn index)
  | XBVar  : i: C.index_lookup c -> exp_base t c (C.get_index c i)
  // free variables
  //  the types in the variable must be t.ty (which is eqtype) because we need to compare the types of variables
  | XVar   : #valty: t.ty -> x: C.var valty -> exp_base t c valty

noeq
type exp (t: table u#i u#j) (c: context t): t.ty -> Type u#(max i j) =
  | XBase: #valty: t.ty -> exp_base t c valty -> exp t c valty
  | XApps: #valty: t.ty -> exp_apps t c (FTVal valty) -> exp t c valty

  // v fby e
  // XXX: the type of value must be at least `eqtype`, but really it should be a pure value type (t.ty) since we should only store pure values in buffers (not, eg, a mutable buffer, if we had such values)
  // in fact, for translation to normalised systems, we need it to be a value type
  | XFby   : #valty: t.ty -> v: t.ty_sem valty -> exp t c valty -> exp t c valty
  // e -> e'
  // Disabled: do we get anything from this? Not yet - maybe if we want unguarded `pre` later
  // | XThen  : #valty: t.ty -> exp t c valty -> exp t c valty -> exp t c valty
  // µx. e[x]
  //  this has to be a pure value type for the same reason as fby: recursive occurrences must be guarded by a fby, so any values will almost certainly need to be stored in a buffer
  | XMu    : #valty: t.ty -> exp t (valty :: c) valty -> exp t c valty
  // let x = e in e[x]
  // XXX: I have relaxed this from (valty: t.ty) to arbitrary type 'a: this makes it easier to infer `XLet e1 e2`
  | XLet   : #valty: t.ty -> b: t.ty -> exp t c b -> exp t (b :: c) valty -> exp t c valty

  // Proof terms
  // Contracts for hiding implementation:
  //   (λx. { assumptions } body { λr. guarantees })(arg)
  // The rely, guarantee and implementation are *expressions*
  // X We need to be able to talk about their semantics in the definition here to
  // X bundle up the proof that the implementation satisfies its contract:
  //   ALWAYS rely ==> ALWAYS guar(impl)
  //
  // X If we made these expressions, it would be difficult to state the contract
  // X because we haven't defined the semantics of expressions yet.
  | XContract:
    #valty: t.ty                      ->
    status: PM.contract_status        ->
    rely: exp t c            t.propty ->
    guar: exp t (valty :: c) t.propty ->
    impl: exp t c            valty    ->
    exp t c valty

(*
  XXX:
  this doesn't play nicely with substitution, because we need to substitute into impl,
  but we don't want to have to re-check the whole implementation each time.
  we really want:

  | XContract:
    #argty: t.ty                      ->
    #valty: t.ty                      ->
    status: PM.contract_status        ->
    rely: exp t c              t.propty ->
    guar: exp t (valty :: c)   t.propty ->
    impl: exp t [argty]        valty    ->
    arg:  exp t c              argty    ->
    exp t c valty


  another obvious attempt would be
  | XContract:
    #argty: t.ty                      ->
    #valty: t.ty                      ->
    status: PM.contract_status        ->
    rely: exp t [argty]        t.propty ->
    guar: exp t [valty, argty] t.propty ->
    impl: exp t [argty]        valty    ->
    arg:  exp t c              argty    ->
    exp t c valty

  but this doesn't let us perform CSE on the rely and the guar

*)


  // check "" e
  | XCheck : PM.prop_status -> exp t c t.propty -> exp t c t.propty
and
 exp_apps (t: table) (c: context t): funty t.ty -> Type =
  // primitives
  | XPrim  : p: t.prim -> exp_apps t c (t.prim_ty p)
  // f(e,...)
  | XApp   : #arg: t.ty -> #ret: funty t.ty -> exp_apps t c (FTFun arg ret) -> exp t c arg -> exp_apps t c ret


let
 exp_bind (t: table) (b: t.ty) (c: context t) (valty: t.ty): Type =
   exp t (b :: c) valty

let weaken_base (#c c': context 't) (#a: ('t).ty) (e: exp_base 't c a): Tot (exp_base 't (C.append c c') a) =
  match e with
  | XVal v -> XVal v
  | XBVar i' ->
    CP.lemma_append_preserves_get_index c c' i';
    XBVar (i' <: C.index_lookup (C.append c c'))
  | XVar x' -> XVar x'

let rec weaken (#c c': context 't) (#a: ('t).ty) (e: exp 't c a): Tot (exp 't (C.append c c') a) (decreases e) =
  match e with
  | XBase e1 -> XBase (weaken_base c' e1)
  | XApps e1 -> XApps (weaken_apps c' e1)
  | XFby v e -> XFby v (weaken c' e)
  | XMu e1 -> XMu (weaken c' e1)
  | XLet b e1 e2 -> XLet b (weaken c' e1) (weaken c' e2)
  | XCheck ps e1 -> XCheck ps (weaken c' e1)
  | XContract ps r g i -> XContract ps (weaken c' r) (weaken c' g) (weaken c' i)
and weaken_apps (#c c': context 't) (#a: funty ('t).ty) (e: exp_apps 't c a): Tot (exp_apps 't (C.append c c') a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f e -> XApp (weaken_apps c' f) (weaken c' e)
