(* Post-processing pass on core expressions: inline trivial XLet aliases.

   For an `XLet b atom body` whose right-hand side is an `XBase` atom
   (`XVal`, `XBVar`, or `XVar`), substitute the atom into the body and
   drop the binding.

   Motivation: the source-to-core lifter introduces gratuitous aliases of
   the form `let x = some_bound_var in 0 fby x` when applying a primitive
   like `fby_core` (whose body refers to its stream argument via `XBVar 0`).
   Inside a `rec`, such aliases trip the deliberately-conservative
   `Pipit.Exp.Causality.causal` check, even though the program is causal
   after inlining. Running `simplify` on a lifted core eliminates those
   aliases so the causality / extractability check succeeds.

   Note that the rewrite is purely structural and bottom-up: we never
   need to re-simplify the substituted body because the substitution
   replaces an `XBVar` leaf with another atom, which cannot turn a
   non-`XBase` right-hand side into an `XBase` one.

   Soundness: [simplify] must preserve the bigstep semantics. The proof
   reduces to the `BSLet` rule for [XLet b e1 e2] (which already evaluates
   by substituting [e1] into [e2]) combined with congruence of [bigstep]
   under [subst1] when the substituted expression is an [XBase] atom.
   The preservation lemma [bigstep_simplify] is stated below and is
   currently admitted; see TODO. *)
module Pipit.Exp.SimplifyLet

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.Exp.Binding
open Pipit.Exp.Bigstep

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

let rec simplify (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot (exp t c a) (decreases e) =
  match e with
  | XBase _ -> e
  | XApps app -> XApps (simplify_apps app)
  | XFby v e1 -> XFby v (simplify e1)
  | XMu e1 -> XMu (simplify e1)
  | XLet b e1 e2 ->
    let e1' = simplify e1 in
    let e2' = simplify e2 in
    (match e1' with
     | XBase _ -> subst1 e2' e1'
     | _ -> XLet b e1' e2')
  | XCheck name e1 -> XCheck name (simplify e1)
  | XContract ps r g impl ->
    XContract ps (simplify r) (simplify g) (simplify impl)

and simplify_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot (exp_apps t c a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f arg -> XApp (simplify_apps f) (simplify arg)


(* ------------------------------------------------------------------------ *)
(* Soundness                                                                *)
(* ------------------------------------------------------------------------ *)

(* [simplify] preserves bigstep semantics: any value reached by [e] under
  streams [rows] is also reached by [simplify e] under the same streams,
  and vice versa.

  Proof sketch (mutual induction on the bigstep derivation):
  * All structural cases ([XBase], [XApps], [XFby], [XMu], [XCheck],
    [XContract]) follow from the IH on subexpressions plus the matching
    bigstep rule for the same head.
  * For [XLet b e1 e2]: by IH, [bigstep rows e1 v1] iff
    [bigstep rows (simplify e1) v1], and [bigstep rows (subst1 e2 e1) v]
    iff [bigstep rows (subst1 (simplify e2) (simplify e1)) v] (the latter
    requires a substitution-congruence lemma on [bigstep]).
    - If [simplify e1] is not [XBase], rewrap with [BSLet] / [BSLet] to
      preserve the [XLet] head.
    - If [simplify e1] is [XBase], the result is [subst1 (simplify e2)
      (simplify e1)], and the [BSLet] rule already evaluates [XLet]
      by substitution, so the witness is essentially the same derivation
      without the outer [BSLet] wrapper.

  TODO:ADMIT prove [bigstep_simplify]. The key auxiliary lemma is
  substitution-congruence of [bigstep] for [XBase] payloads, which
  should follow from the existing machinery in [Pipit.Exp.Binding.Properties]. *)
val bigstep_simplify
  (#t: table u#i u#j)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a)
  (v: t.ty_sem a)
  : Lemma (bigstep_prop rows e v <==> bigstep_prop rows (simplify e) v)
let bigstep_simplify #_ #_ #_ _ _ _ = admit ()

