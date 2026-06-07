# TTCan2 — workaround notes

This is the port of `example/ttcan/` to the new lifter pipeline
(`#lang-pipit` + `lift_ast_tac1`). A handful of features in the new
pipeline aren't there yet, so the source files in this directory work
around them. Each numbered item below is an outstanding gap in
`Pipit.Plugin.Lift` / `Pipit.Source.Ast.Lower` to revisit; the
corresponding workaround in this directory should be reverted once the
gap is closed.

## Status

Verified (fully ported, all VCs discharged):

  - `Network.TTCan.Types.*`
  - `Network.TTCan.Prim.*`
  - `Network.TTCan.Abstract.Schedule`
  - `Network.TTCan.Impl.Util`
  - `Network.TTCan.Impl.States` (all six state machines)

Partially ported:

  - `Network.TTCan.Impl.Triggers` — non-streaming helpers
    (`trigger_load_raw`, `trigger_load`, `is_started`,
    `trigger_absolute_time`, `prefetch_index`) and the input-validity
    stream (`trigger_input_valid`) are in place. The streaming
    `prefetch` / `fetch` (and the abandoned `prefetch_result_valid` /
    `fetch_result_valid` contracts) are not ported. Blocked on
    workarounds 5 and 6: the original `prefetch` is a record-typed
    `rec'` that projects `fetch.index`, `fetch.enabled`, and
    `fetch.time_mark` directly off the recursive stream.
  - `Network.TTCan.Impl.Errors` — pure helpers (`no_error`, `summary`,
    `transient`, `cycle_end_check`) are in place. `scheduling_error_1`
    is not yet ported. It calls `Clocked.get_or_else` and `S32R.{min,
    max, dec_sat}` on stream args; the analogous patterns work
    elsewhere in `Impl.States` and in `Plugin.Test.Bug.CrossModHelper`,
    so the actual blocker is unknown — needs an attempt.
  - `Network.TTCan.Impl.MessageStatus` — `status_update` plus the
    three constants (`increment` / `decrement` / `nothing`) are
    present. `message_status_counters` and `rx_pendings` are not yet
    ported (both are `rec'` over an array threaded through
    `MSC64.update` / `BV64I.set`). Whether the cross-module
    `MSC64.*` / `BV64I.*` calls hit a real lifter gap (see workaround
    3) is untested — the helper-on-stream-args probe in
    `Plugin.Test.Bug.CrossModHelper` passes, so the assumption that
    those helpers must move under `#lang-pipit` is unverified.

Not yet ported (stubbed modules):

  - `Network.TTCan.Impl.Controller` — depends on the missing streaming
    pieces of `Impl.Triggers`, `Impl.MessageStatus`, and
    `Impl.Errors`, plus the `Clocked.map` / record-projection patterns
    (workarounds 5, 6) and `let open U64` / `let open S32R`
    (workaround 7).
  - `Network.TTCan.TriggerTimely` — depends on `Pipit.Sugar.Check` /
    `Pipit.Sugar.Contract` (workaround 9) and on static `cfg`
    parameters threaded through contract-typed streams.
  - `Network.TTCan.Extract` — Pulse extraction wrapper; deliberately
    left for last (see section 8).

## 1. Multi-arm `match` on stream scrutinee

**Gap.** `Pipit.Source.Ast.Lower` (~line 547):
`"AMatch on stream scrutinee is not yet supported"`. Only static
scrutinees are accepted (`AppPureConst`).

**Workaround.** Rewrite to a chain of `if scrut = Ctor1 then ... else if scrut = Ctor2 then ...`.
This only works when the scrutinee type is an `eqtype` enum (which
covers `mode`, `sync_mode`, `master_mode`, `error_severity`, etc. here).

## 2. `has_stream config` (top-level static param)

**Status.** Already resolved for our usage in this port. Top-level
`(cfg: config)` is classified as a Static binder by `lift_top_body`,
so it does NOT trigger `has_stream config` resolution.
The 2026-06-01 partial-application fix in `Reflect.lift_app_fv`
additionally pre-applies splice-safe Static args (including
`cfg.field.subfield`) at the splice point, so projections like
`cfg.triggers.ttcan_exec_period` survive the lift without demanding
an instance for `config`.

**Where it still bites.** Anywhere `cfg` is forced into a stream
context (e.g. passed as a stream arg to an APrim helper), `funty_of`
calls `has_stream config`, which fails because `config` has function
fields (`triggers.trigger_read`) and isn't `eqtype`. Fix: keep `cfg`
on the static side (param of the lifted binding, never embedded in a
stream tuple).

## 3. Cross-module non-stream helpers called from `#lang-pipit`

**Status (2026-06-08).** No reproducer remains. The original symptom
("`Variable XYZ not found` at the static lower pass when a `let`-bound
stream local flows into a plain F\* helper from outside `#lang-pipit`")
is contradicted by `pipit/plugin-test/Plugin.Test.Bug.CrossModHelper.fst`,
which exercises:

  - direct call (`H.opt_get_or_else dflt clck` with stream-bound `dflt`),
  - the same call inside a `rec'` feedback loop (mirroring the original
    `States.cycle_time_capture` shape that motivated the workaround), and
  - a two-stream-arg variant.

All three pass against a sibling helpers module
(`Plugin.Test.Bug.CrossModHelper.Helpers`) that is plain F* — not
`#lang-pipit`, no `[@@source_mode]`. The TTCan-side evidence agrees:
`Impl.States` calls `Clocked.{get_or_else, get_clock, get_value,
current_or_else}` and `S32R.{inc_sat, dec_sat, op_*, s32r}` directly
on stream args throughout, with no wrappers.

**Where it might still bite.** `MSC64.{index, update}` and
`BV64I.{set, clear}` are not yet exercised on stream args by anything
that verifies — the only call sites are inside the still-stubbed
`message_status_counters` / `rx_pendings`. The hypothesis that they
need to be moved under `#lang-pipit` (or annotated `[@@source_mode]`)
is unverified. The right next step is to try porting one of those two
bindings and see what (if anything) breaks.

**If a regression resurfaces**, the historical workarounds were:
  - Put the helper module under `#lang-pipit` (the way
    `Network.TTCan.Prim.Clocked` and `Network.TTCan.Prim.U64` are here)
    so the helper gets a `_core` that `lift_app_fv` can find; or
  - Hoist the offending stream local to a top-level monomorphic
    wrapper so the static-lower walker sees a Static binder.

## 4. `pre #T expr` — explicit type-arg uses on `pre`

**Status (2026-06-08).** No reproducer remains. Both `pre s` (implicit
type-arg) and `pre #int s` lift cleanly, as does
`pre #(option int) s` where the type-arg is itself parameterised by
another `has_stream` instance. See
`pipit/plugin-test/Plugin.Test.Bug.PreExplicitType.fst` for the
regression probe; if a future change re-breaks the explicit form,
comment out the failing case in that file and re-add this workaround.

## 5. `Clocked.map` with anonymous lambdas

**Gap.** `Clocked.map f c` where `f` is a `(fun x -> ...)` literal
isn't liftable — the lifter reports
`Pipit.Source.Ast.Reflect: unsupported term shape: fun p -> p.px`.

**Workaround.** For pure record-field projections, use the projector
constant directly: `Clocked.map Mkref_message?.sof last_ref` (covered
by §6, which is no longer a workaround). For non-projection bodies,
hoist the lambda to a named top-level `let`, or inline a
`if Clocked.get_clock c then Some <body of get_value c> else None`.

See `pipit/plugin-test/Plugin.Test.Bug.MapLambda.fst` for the live
probe (passing-baseline + commented-out failing case).

## 6. Record projections as first-class function values

**Status (2026-06-08).** No reproducer remains. Both `map Mkpoint?.px c`
and `map Mkref_t?.cycle_index c` lift cleanly when `map` is a plain
`(#a #b: eqtype) (fn: a -> b) (clck: clk a): clk b` polymorphic helper.
See `pipit/plugin-test/Plugin.Test.Bug.MapProjector.fst` for the
regression probe; if a future change re-breaks the projector form,
comment out the failing case in that file and re-add this workaround.

Note: the §5 anonymous-lambda case (e.g. `map (fun p -> p.px) c`) is
still live — see `Plugin.Test.Bug.MapLambda` for that probe.

## 7. `let open M` inside `#lang-pipit`

**Status (2026-06-08).** No reproducer remains. `FStar.UInt64`
arithmetic (`+%^`, `-%^`, `*%^`) and comparison (`<^`) operators all
lift cleanly inside a `let open U64 in ...` block. See
`pipit/plugin-test/Plugin.Test.Bug.LetOpenOps.fst` for the regression
probe; if a future change re-breaks operator resolution under
`let open`, comment out the failing cases in that file and re-add
this workaround (mechanical replacement table available in git
history).

## 8. Pulse extraction (`Network.TTCan.Extract.fst`)

**Status.** Deliberately skipped for now. `example/ttcan/` uses
`Pipit.Sugar.Base.system_of_stream` and the legacy `tac_extract`
infrastructure. Re-introduce after Controller is ported and after we
decide on a Pulse-extraction surface for the new pipeline.

## 9. `Pipit.Sugar.{Check, Contract}` (TriggerTimely)

**Gap.** `Pipit.Sugar.Check` / `Pipit.Sugar.Contract` are deleted in
the new pipeline.

**Workaround.** Use the `: Stream tau (requires R) (ensures G)` return
type sugar that the preprocessor in `#lang-pipit` splits into the
expected `_rely` / `_guar` / `body` triple (see
`pipit/plugin-test/Plugin.Test.Source.Contract.fst` for the canonical
test of this sugar). Drop the `assert (... system_induct_k1 ...) by
(pipit_simplify ...)` boilerplate — `proof_induct1` /
`proof_expect_failure` attributes drive the contract proof obligations
in the new pipeline.

## C. `open` order when both user and `Pipit.Source` define `mode`

**Gap.** `Pipit.Source` re-exports `Pipit.Plugin.Interface` which
defines `type mode = | Stream | Static | ModeFun ...`. If the user's
`open` of their domain module (which also defines a `mode` enum, e.g.
`Network.TTCan.Types.Base.mode`) appears BEFORE `open Pipit.Source`,
the plugin's `mode` shadows the user's. After the preprocessor strips
`stream` from `(m: stream mode)`, F* resolves the annotation to the
plugin's `mode` and the body's `m = Mode_Ctor` fails with
`"mode is not equal to the expected type ...Base.mode"`.

**Workaround.** Put `open Pipit.Source` first (or qualify the
conflicting binders / open the user module last). In ttcan2:

```fst
#lang-pipit
open Pipit.Source
open Network.TTCan.Types
```

---

## Resolved lifter bugs

### A. ~~Cross-module `Clocked.t`-arg in `let rec` / `rec'` body~~ (RESOLVED 2026-06-03)

Fixed in `Pipit.Plugin.Lift.resolve_inst`: when the queried `has_stream`
type is closed over ground FVars, the lifter now returns `None` so a
single `_ by FStar.Tactics.Typeclasses.tcresolve ()` placeholder picks
the dictionary at both callsites. Without the fix, the lifter
synthesised independent `_ by tcresolve()` uvars per callsite;
combined with the non-unfold `Pipit.Prim.HasStream.shallow`, two
printer-identical `shallow (Clocked.t T)` terms failed to unify and
the subtype check was punted to SMT as an opaque
`forall any_result. shallow X == any_result ==> ...` goal.

Regression test: `pipit/plugin-test/Plugin.Test.Bug.PolyInstance.fst`
(`probe_rec_with_t`).

### B. ~~Refined-return-type instances leaking into hoisted helpers~~ (RESOLVED 2026-06-05)

Symptom (e.g. `States.tx_ref_messages`): a then-branch returning a
refined type like
`S32R.inc_sat cyc_idx : s: t b { S32R.v s >= S32R.v cyc_idx /\ ... }`
caused the lifted `__xprim_*` top-level helper to be emitted with the
refinement leaking into its argument types, mentioning the
out-of-scope local `cyc_idx` (Error 230 "Variable cyc_idx not found").
Lifting refined constants to a top-level
`let msc_max: message_status_counter = S32R.s32r 7` also hung the
elaborator (typeclass resolution loops > 2 min) for the same reason.

Fixed in `Pipit.Source.Ast.Reflect.lift_ite`: the
`T.tc e.oe_tac_env t_tm` result-type call is now wrapped in
`strip_refinements` (see lines 597–603), matching the existing strip
calls in `of_prim_fv_applied`, `lift_top_body`, `lift_app_fby`, and
`pat_of_fstar`. After the fix, all Bug B workaround locals
(`ref_zero` / `ref_max` / `mi_zero` in `ref_trigger_offsets`,
`ci_zero` in `tx_ref_messages`) were removed from `Impl.States.fst`;
inline `S32R.s32r N` now works directly inside `#lang-pipit` bodies.

### D. ~~Lifter blow-up on `stream (option T) = Some <static>` equality~~ (RESOLVED 2026-06-05)

Symptom: `States.master_modes` and `States.tx_ref_messages` took
multiple minutes to verify, with `tx_ref_messages` killed after 13 min
at 4.4 GB RSS. Originally bisected (see
`pipit/plugin-test/Plugin.Test.Bug.MasterModes.V2b`) to the
`ref_msg = Some master_idx` shape; the manual workaround was to
project clock + payload separately
(`let ref_clk = Some? ref_msg in let ref_idx = match ref_msg with ...`).

Fixed by the 2026-06-04 / 2026-06-05 lifter changes:

  1. Hoisting of synthesized prim/ctx helpers to top-level `let`s,
     with discharge gated by `core_lifted_ctx` / `core_lifted_prim`
     attributes rather than `Unfold_for_unification_and_vcgen`; and
  2. The `lift_ite` `strip_refinements` fix above, which prevents the
     nested if/else chain from baking refinements into every
     `p'select` argument type.

`States.master_modes` and `States.tx_ref_messages` now use the
straightforward `if ref_msg = Some master_index then ...` form
directly. The V2b regression test (`Plugin.Test.Bug.MasterModes.V2b`)
verifies in 6.62 s (baseline > 5 GB hang; intermediate measurements
24 s after hoisting, 7.83 s after attribute-delta, 6.62 s after the
`lift_ite` refinement strip).
