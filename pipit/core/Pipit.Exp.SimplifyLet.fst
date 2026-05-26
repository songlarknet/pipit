(* Post-processing pass on core expressions: inline trivial XLet aliases.

   For an `XLet b atom body` whose right-hand side is an `XBase` atom
   (`XVal`, `XBVar`, or `XVar`), substitute the atom into the body and
   drop the binding.

   This is intended to be a semantics-preserving rewrite; the proof of
   bigstep preservation is left as future work.

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
   non-`XBase` right-hand side into an `XBase` one. *)
module Pipit.Exp.SimplifyLet

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.Exp.Binding

module C = Pipit.Context.Base

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
