(* Demos for the `lemma_pattern` hint combinator from `Pipit.Source`.
   See the "Lemma combinator" entry of
   doc/roadmap/v1-source-followups.md for design context.

   Usage shape:

     1. Define a unit-typed pattern marker function (`irreducible` so
        the marker call survives normalisation).
     2. Define a top-level `Lemma … [SMTPat marker_call]` that fires
        on it.
     3. Call `lemma_pattern (marker_call …)` from inside a streaming
        body so the marker term is baked into the spliced core's
        obligation.

   This mirrors the historical TTCAN trick
   (`lemma_adequate_spacing_next_inc` + `_pattern`); the combinator
   itself lives in `Pipit.Source` as a plain `#lang-pipit` source
   helper, so no Source / plugin / core changes are required to
   adopt it.

   Demo 1: positive case. The `lemma_pattern (…)` call survives the
   lift, the SMTPat fires, and `[@@proof_induct1]` discharges.

   Demo 2: negative control. Same body as Demo 1 but without the
   `lemma_pattern (…)` call; tagged `proof_expect_failure` so the
   module typechecks iff `[@@proof_induct1]` actually fails to
   discharge. This pins down the claim that the marker call is what
   makes the SMTPat fire.

   Demo 3: recursive case (TTCAN shape). The marker takes the
   recursive-binding variable as its argument; 1-induction *is*
   strong enough here because the lifted obligation is shaped
   `seed >= 0 ==>^ prev >= 0 ==>^ goal`, so the SMTPat fires once
   `prev >= 0` enters the hypothesis at each step. *)
module Plugin.Test.Source.Lemma
#lang-pipit

open Pipit.Source


(*** Shared opaque payload ***)

(* An `assume val` primitive: SMT sees an uninterpreted function. The
   plugin lifts it via `of_prim_fv_applied`, which only consults the
   F* type — no body required at lift time. *)
assume val opaque_double (x: int): int

irreducible
let lemma_opaque_double_pattern (x: int): unit = ()

(* The lemma is the only thing tying `opaque_double` to anything Z3
   can reason about. *)
let lemma_opaque_double (x: int)
  : Lemma
    (requires x >= 0)
    (ensures opaque_double x >= 0)
    [SMTPat (lemma_opaque_double_pattern x)]
  = admit ()


(*** Demo 1 — positive: marker call routes the SMTPat into the obligation ***)

[@@proof_induct1]
let eg_opaque (x: stream int): stream int =
  lemma_pattern (lemma_opaque_double_pattern x);
  check ((x >= 0) ==>^ (opaque_double x >= 0));
  opaque_double x


(*** Demo 2 — negative control: same body, no marker call ***)

(* Without `lemma_pattern (lemma_opaque_double_pattern x)`, the lifted
   obligation has nothing that matches `[SMTPat (lemma_opaque_double_pattern x)]`,
   so `lemma_opaque_double` never fires, and the check can't discharge.
   `proof_expect_failure` makes the module typecheck iff that's what
   actually happens. *)
[@@proof_induct1; proof_expect_failure]
let eg_opaque_no_pattern (x: stream int): stream int =
  check ((x >= 0) ==>^ (opaque_double x >= 0));
  opaque_double x


(*** Demo 3 — recursive case (TTCAN shape) ***)

(* TTCAN's `lemma_adequate_spacing_next_inc_pattern` shape: the marker
   takes the recursive-binding variable as an argument. *)
irreducible
let lemma_double_prev_pattern (n: int): unit = ()

assume val lemma_double_prev (n: int)
  : Lemma
    (requires n >= 0)
    (ensures opaque_double n - n >= 0)
    [SMTPat (lemma_double_prev_pattern n)]

(* 1-induction is enough here: the lifted obligation is
     `(seed >= 0) ==>^ ((prev >= 0) ==>^ (opaque_double prev - prev >= 0))`,
   so at each step `prev >= 0` is in the hypothesis and the SMTPat on
   `lemma_double_prev_pattern prev` fires directly. The marker call
   takes the recursive variable as its argument, mirroring TTCAN's
   `lemma_adequate_spacing_next_inc_pattern prev_inc` shape. *)
[@@proof_induct1]
let eg_opaque_in_rec (seed: stream int): stream int =
  let rec acc =
    let prev = 0 `fby` acc in
    lemma_pattern (lemma_double_prev_pattern prev);
    check ((seed >= 0) ==>^ ((prev >= 0) ==>^ (opaque_double prev - prev >= 0)));
    prev + seed
  in acc


(*** Findings ***)

(* Status: the `lemma_pattern` / `check_pattern` / `check_pattern_true`
   combinators live in `Pipit.Source`. This module is the demo /
   regression test that exercises them end-to-end via `[@@proof_induct1]`.

   What works (zero plugin / core changes; the combinator is a plain
   `#lang-pipit` source helper):

   1. `lemma_pattern (p: unit): unit = check (check_pattern p)` lifts
      cleanly through the existing AST pipeline. Demo 1 confirms the
      SMTPat trigger survives the lift and `[@@proof_induct1]`
      discharges the obligation.

   2. Demo 2's `proof_expect_failure` confirms the negative direction:
      without the `lemma_pattern (…)` call, `lemma_opaque_double` has
      nothing to match on and the check cannot discharge. The
      `lemma_pattern (…)` call really is what's pulling the SMTPat
      into the obligation.

   3. Demo 3 demonstrates the same shape inside a recursive binding
      and passes with plain `[@@proof_induct1]`. The lifted
      obligation is `seed >= 0 ==>^ prev >= 0 ==>^ goal`, so
      `prev >= 0` is in the hypothesis at every step and the SMTPat
      on `lemma_double_prev_pattern prev` discharges the goal
      directly. (Note: a stronger TTCAN-style invariant that
      threads `seed >= 0` through to a non-trivial conclusion about
      the accumulator value itself would still need contracts or
      `proof_induct k`.)

   4. The user writes the pattern marker and the `Lemma … [SMTPat …]`
      themselves, in the same shape that TTCAN's
      `lemma_adequate_spacing_next_inc` + `_pattern` used. The marker
      needs to be `irreducible` (or the discharge `norm_full` will
      eat the trigger before the SMT encoder sees it).

   Encoding traps spotted along the way (kept here for posterity):

   * `check (p = ())` doesn't work: `op_Equality #unit` is decidable
     (unit is a singleton) so the SMT encoder folds both sides to
     `()` and the marker subterm is lost.
   * `irreducible let check_pattern (pat: unit): bool = true` keeps
     the marker subterm visible but the obligation `check_pattern p
     = true` is unprovable — SMT treats irreducible bodies as
     uninterpreted (same as `assume val`).
   * The assume-val + SMTPat-lemma encoding actually used gets both:
     opaque to the encoder (trigger survives) AND a paired SMTPat
     lemma to discharge the wrapper obligation. The lemma fires
     unconditionally on any `check_pattern p`, so it costs nothing
     beyond a single SMTPat hit per `lemma_pattern` call.

   What's missing (deferred):

   * No auto-synthesis of the marker / `Lemma` from a `lemma_blagh
     x y; …` call yet — that's the "Later" bullet of the roadmap
     entry. Once a real consumer (TTCAN) exercises the combinator,
     the plugin can synthesise the unit-typed marker + skeleton
     `Lemma … [SMTPat …]` decl from a single user call.

   * No diagnostic for failed firings: if the SMTPat preconditions
     don't hold in the spliced transition system, the lemma silently
     contributes nothing and the user sees a bare check failure (or
     in Demo 2's case, no failure at all if it was supposed to fire
     but didn't). The `XHint` alternative (also in the roadmap
     entry) would address this by letting the discharge tactic
     *report* missed hints. *)
