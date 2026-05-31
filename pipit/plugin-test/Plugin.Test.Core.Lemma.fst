(* Experiment: encoding lemma instantiation via SMT patterns inside
   #lang-pipit-style bodies. See the "Lemma combinator" entry of
   doc/roadmap/v1-source-followups.md for context.

   The shape the user gets:
     1. a unit-typed pattern marker function (`irreducible` so the
        marker call survives normalisation),
     2. a top-level `Lemma … [SMTPat marker_call]` that fires on it,
     3. a call to `lemma_pattern (marker_call …)` from inside a
        streaming body so the marker term ends up baked into the
        spliced core's obligation.

   The historical (pre-cleanup) encoding (git show 4cee216) was
     let lemma_pattern: stream unit -> stream unit =
       Check.exp_of_stream1 (fun pat -> check "" (pat = const ()))
   i.e. `lemma_pattern p` reduces to `check (p = ())`. This file is
   the same idea, expressed as a plain `#lang-pipit` source helper so
   no Source / plugin / core changes are required. The discharge
   wrapper for the non-recursive case verifies, confirming that the
   SMTPat triggered by `lemma_pattern` actually fires on the lifted
   obligation.

   Encoding choice: `lemma_pattern p` lifts to `check (check_pattern p)`
   where `check_pattern` is an `assume val (pat: unit): bool` paired
   with a `check_pattern_true` SMTPat lemma that unconditionally
   discharges `check_pattern p = true`. Two simpler encodings we
   considered and discarded:

   * `check (p = ())` — SMT encoder collapses `op_Equality #unit a b`
     to `True` (unit is a decidable singleton), erasing the marker
     subterm from triggering position.
   * `irreducible let check_pattern (pat: unit): bool = true` — keeps
     the marker subterm visible but the SMT encoder treats the body
     as uninterpreted (same as `assume val`), so the `check_pattern p
     = true` obligation has no truth witness and can't discharge.

   The assume-val + SMTPat-lemma pair gets both properties: opacity
   (so `check_pattern (marker x)` survives into the SMT query as a
   trigger candidate for the user's lemma on `marker x`) AND
   provability (the wrapper obligation discharges via the paired
   lemma). *)
module Plugin.Test.Core.Lemma

open Pipit.Source

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
module PSSB = Pipit.Prim.HasStream
module PPS = Pipit.Prim.Shallow
module PXB = Pipit.Exp.Base
module PXCB = Pipit.Exp.Checked.Base
module SI = Pipit.System.Ind
module SX = Pipit.System.Exp
module PT = Pipit.Tactics

#set-options "--print_implicits --print_bound_var_types --print_full_names"
// Useful when debugging:
// #set-options "--ext pipit:lift:debug"


(*** User-written hint combinator ***)

(* `lemma_pattern m` is a stream-level no-op (returns `()`), but the
   spliced core retains an SMT-visible reference to `m` because the
   `check` obligation mentions it. The user is responsible for
   defining `m` as a top-level unit-typed marker and pairing it with a
   `Lemma … [SMTPat (m …)]` so the lemma fires on the obligation.

   `check_pattern p` is a `bool`-valued wrapper around the marker call
   so the `check` obligation becomes `check_pattern p = true` rather
   than the awkward `p = ()`. Encoded as an `assume val` so the SMT
   encoder treats it as an uninterpreted function symbol (and the
   marker subterm `p` survives as a triggering argument). The paired
   `check_pattern_true` SMTPat lemma discharges the wrapper obligation
   unconditionally, leaving the user's marker lemma free to do the
   real work on the rest of the goal.

   Why not `irreducible let check_pattern p = true`? The body would
   need to be visible to SMT to discharge `check_pattern p = true`,
   but visible to SMT means the encoder may inline it as plain `true`
   and erase `p` from triggering position. The assume-val + SMTPat
   pair gets both: opacity (the trigger survives) and provability
   (the obligation discharges). *)

assume val check_pattern (pat: unit): bool

assume val check_pattern_true (pat: unit)
  : Lemma (check_pattern pat = true) [SMTPat (check_pattern pat)]

[@@source_mode (ModeFun Stream true Stream)]
let lemma_pattern (p: unit): unit =
  check (check_pattern p)
%splice[] (PPL.lift_ast_tac1 "lemma_pattern")


(*** Demo 1 — minimal opaque payload, lemma actually needed ***)

(* An `assume val` primitive: SMT sees an uninterpreted function. The
   plugin lifts it via `of_prim_fv_applied`, which only consults the
   F* type — no body required at lift time. *)
assume val opaque_double (x: int): int

irreducible
let lemma_opaque_double_pattern (x: int): unit = ()

(* The lemma is the only thing tying `opaque_double` to anything Z3
   can reason about. Without the SMTPat firing, the check below
   cannot discharge. *)
let lemma_opaque_double (x: int)
  : Lemma
    (requires x >= 0)
    (ensures opaque_double x >= 0)
    [SMTPat (lemma_opaque_double_pattern x)]
  = admit ()

[@@source_mode (ModeFun Stream true Stream)]
let eg_opaque (x: int): int =
  lemma_pattern (lemma_opaque_double_pattern x);
  check ((x >= 0) ==>^ (opaque_double x >= 0));
  opaque_double x
%splice[] (PPL.lift_ast_tac1 "eg_opaque")

(* Discharge wrapper: the same shape as Plugin.Test.Core.Check's
   `eg_check_trivial_check`. If the SMTPat does *not* fire, the
   `induct1 sys` query reduces to an uninterpreted
   `opaque_double x >= 0` obligation and times out / fails.
   Verified — the trigger survives the lift through `lemma_pattern`. *)
[@@core_of_source (`%eg_opaque) (ModeFun Stream true Stream)]
let eg_opaque_check: PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int) =
  let unfold e = eg_opaque_core in
  let unfold sys = SX.system_of_exp e in
  assert (SI.induct1 sys) by (PT.norm_full []);
  PXCB.bless e


(*** Demo 2 — same idea inside `rec'`, matching the TTCAN shape ***)

(* TTCAN's `lemma_adequate_spacing_next_inc_pattern` shape: the marker
   takes the recursive-binding variable as an argument. *)
irreducible
let lemma_double_prev_pattern (n: int): unit = ()

assume val lemma_double_prev (n: int)
  : Lemma
    (requires n >= 0)
    (ensures opaque_double n - n >= 0)
    [SMTPat (lemma_double_prev_pattern n)]

[@@source_mode (ModeFun Stream true Stream)]
let eg_opaque_in_rec (seed: int): int =
  rec' (fun acc ->
    let prev = 0 `fby` acc in
    lemma_pattern (lemma_double_prev_pattern prev);
    check ((seed >= 0) ==>^ ((prev >= 0) ==>^ (opaque_double prev - prev >= 0)));
    prev + seed)
%splice[] (PPL.lift_ast_tac1 "eg_opaque_in_rec")

(* No discharge wrapper for the rec' case yet: it would require
   strengthening the induction invariant to maintain `prev >= 0`
   across steps (which depends on `seed >= 0`, hence the implication
   form above). The lifting itself succeeds; the discharge is left
   for the contract / proof-induct-k work to address. The point of
   the rec' demo is that `lemma_pattern` lifts and survives into the
   obligation in the recursive shape too. *)


(*** Findings ***)

(* What works today (vanilla helper, zero Source / plugin / core
   changes):

   1. `lemma_pattern (p: unit): unit = check (check_pattern p)` lifts
      cleanly through the existing AST pipeline (it's a unit-typed
      streaming helper that calls `check`). The non-recursive demo
      discharges via the standard `induct1` + `norm_full` pipeline,
      i.e. the SMTPat trigger survives the lift.

   2. The user can call `lemma_pattern (lemma_blagh_pattern a b c)`
      from any streaming body (including inside `rec'` and after
      other `let`s). The marker call lifts into the spliced core's
      `XCheck` obligation as `check_pattern (lemma_blagh_pattern a b
      c)`, where the user's `[SMTPat (lemma_blagh_pattern …)]` can
      fire.

   3. The user writes the pattern marker and the `Lemma … [SMTPat …]`
      themselves, in exactly the same shape that TTCAN's
      `lemma_adequate_spacing_next_inc` + `_pattern` used. The marker
      needs to be `irreducible` (or the discharge `norm_full` will
      eat the trigger before the SMT encoder sees it).

   Encoding traps spotted along the way:

   * `check (p = ())` doesn't work: `op_Equality #unit` is decidable
     (unit is a singleton) so the SMT encoder folds both sides to
     `()` and the marker subterm is lost.
   * `irreducible let check_pattern (pat: unit): bool = true` keeps
     the marker subterm visible but the obligation `check_pattern p
     = true` is unprovable — SMT treats irreducible bodies as
     uninterpreted (same as `assume val`).
   * The assume-val + SMTPat-lemma encoding used here gets both:
     opaque to the encoder (trigger survives) AND a paired SMTPat
     lemma to discharge the wrapper obligation. The lemma fires
     unconditionally on any `check_pattern p`, so it costs nothing
     beyond a single SMTPat hit per `lemma_pattern` call.

   What's missing (deferred):

   * No auto-synthesis of the marker / `Lemma` from a `lemma_blagh
     x y; …` call yet — that's the "Later" bullet of the roadmap
     entry. Once the experimental shape lands in real consumers,
     the plugin can synthesise the unit-typed marker + skeleton
     `Lemma … [SMTPat …]` decl from a single user call.

   * No diagnostic for failed firings: if the SMTPat preconditions
     don't hold in the spliced transition system, the lemma silently
     contributes nothing and the user sees a bare check failure. The
     `XHint` alternative (also in the roadmap entry) would address
     this by letting the discharge tactic *report* missed hints, but
     that requires a new core constructor and touches every `exp`
     recursor.

   * The discharge for the rec' case still needs proof-induction
     strengthening (covered by the `proof_induct k` work) — the
     lemma-pattern plumbing is orthogonal to that.

   * Promotion: `lemma_pattern`, `check_pattern`, and
     `check_pattern_true` should move from this experimental module
     to `Pipit.Source` once a real consumer (TTCAN) exercises them.
     Three-line copy. *)
