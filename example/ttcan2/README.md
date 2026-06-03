# TTCan2 — workaround notes

This is the port of `example/ttcan/` to the new lifter pipeline
(`#lang-pipit` + `lift_ast_tac1`). A handful of features in the new
pipeline aren't there yet, so the source files in this directory work
around them. Each numbered item below is an outstanding gap in
`Pipit.Plugin.Lift` / `Pipit.Source.Ast.Lower` to revisit; the
corresponding workaround in this directory should be reverted once the
gap is closed.

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

**Gap.** Helpers such as `S32R.inc_sat`, `S32R.dec_sat`, `MSC64.index`,
`MSC64.update`, `BV64I.set`, `BV64I.clear`, `Clocked.get_or_else`,
`Clocked.get_value`, `Clocked.get_clock`, `Clocked.map` are defined as
ordinary F* functions (not `[@@source_mode ...]` annotated, and not
inside a `#lang-pipit` module). When a `#lang-pipit` body calls them
on stream args, the lifter doesn't find a `_core` for them and falls
back to APrim. APrim then classifies the call mode as `AppPureConst`
(static), which is fine for pure helpers — but a `let`-bound *stream*
name that flows into one of those args (e.g. `Clocked.get_or_else dflt clck`
where `dflt` is a stream local) fails name resolution at the static
lower pass ("Variable XYZ not found").

**Workaround.**
  - Put the helper module under `#lang-pipit` (the way
    `Network.TTCan.Prim.Clocked` and `Network.TTCan.Prim.U64` are here).
    This makes the helper itself get lifted and emits a `_core` that
    `lift_app_fv` can find.
  - For helpers we can't easily move (typically ones that mention
    static-only F* features), bind the stream value to a top-level
    let first so the static-lower walker sees a top-level Static
    binder rather than an inner BStream name.

## 4. `pre #T expr` — explicit type-arg uses on `pre`

**Gap.** The preprocessor folds `pre e` into a static binding, but
the explicit `#T` annotation isn't threaded through the lift.

**Workaround.** Drop the `#T` annotation — type inference recovers it.
For values where the implicit `val_default` doesn't typecheck, use
`(PSSB.val_default `fby` v)` explicitly (or a constant of the right
type, e.g. `0uL `fby` v` / `false `fby` v`).

## 5. `Clocked.map` with anonymous lambdas

**Gap.** `Clocked.map f c` where `f` is a `(fun x -> ...)` literal
isn't liftable — the lifter doesn't synthesize a core for the
anonymous function.

**Workaround.** Inline the body. For instance:
`Clocked.map (fun r -> r.sof) last_ref`
becomes a `let`-bound destructure plus inlined construction. In
practice for this port that means manually `if Clocked.get_clock c
then Some <projection of get_value c> else None` or hoisting the
lambda to a named top-level `let`.

## 6. Record projections as first-class function values

**Gap.** `Clocked.map Mkref_message?.cycle_index last_ref` passes the
projector `Mkref_message?.cycle_index` as a first-class function.
The lifter doesn't recognize this as a `_core`.

**Workaround.** Use direct field access at the call-site:
`r.cycle_index` (or wrap with `Clocked.map (fun r -> r.cycle_index) ...`
if a clocked map is needed — see workaround 5; in many cases the
clocked map can be inlined entirely).

## 7. `let open M` inside `#lang-pipit`

**Gap.** Module-open inside a `#lang-pipit` body doesn't fold operator
FQNs the preprocessor expects.

**Workaround.** Use the explicit qualified form: `U64.op_Star x y`
(instead of `let open U64 in x *^ y`), `S32R.op_Less x y` (instead of
`S32R.( x < y )`), etc. Mechanical replacement table:

| infix    | replacement                  |
| -------- | ---------------------------- |
| `a *^ b` | `U64.op_Star a b`            |
| `a +^ b` | `U64.op_Plus a b`            |
| `a -^ b` | `U64.op_Subtraction a b`     |
| `a <^ b` | `U64.op_Less a b`            |
| `a <=^ b`| `U64.op_Less_Equals a b`     |
| `a >^ b` | `U64.op_Greater a b`         |
| `a >=^ b`| `U64.op_Greater_Equals a b`  |
| `a =^ b` | `U64.op_Equals a b`          |

(Same pattern for `S32R`; see `Network.TTCan.Prim.U64`/`.S32R` for the
defined operator names.)

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
expected `_rely`/`_guar`/`body` triple (see
`pipit/plugin-test/Plugin.Test.Source.Contract.fst` for the canonical
test of this sugar). Drop the `assert (... system_induct_k1 ...) by
(pipit_simplify ...)` boilerplate — `proof_induct1` /
`proof_expect_failure` attributes drive the contract proof obligations
in the new pipeline.

## A. Lifter bug: `Clocked.t`-arg in `let rec` / `rec'` body (BLOCKER)

**Gap (no source-level workaround).** Any `let rec x = ...` or
`rec' (fun x -> ...)` whose body passes a `stream (Clocked.t T)`
argument to a function call fails to lift with a printer-identical
subtyping mismatch:

  Expected: ... `(shallow T)`
  Got:      ... `(shallow T)`

Bisected in `Network.TTCan.Impl.States.fst` (see the probe set at the
top of the module):

  - `let rec` + monomorphic call with only `stream ntu` args → PASSES
  - `let rec` + call passing `stream (option ntu)` → PASSES
  - `let rec` + call passing `stream (Clocked.t ntu)` → FAILS
  - `rec'` combinator instead of `let rec` → FAILS the same way
  - Arg order (Clocked first vs last) → no effect
  - Wrapping `Clocked.get_or_else` in a monomorphic `goe_ntu` → no help
  - Adding/removing explicit `instance has_stream_ntu` → no effect
  - Annotating `: ntu` on the result → no effect
  - `<: ntu` ascription → silently ignored

Diagnosis: the issue lives in `Pipit.Source.Ast.Lower` (or
`Pipit.Plugin.Lift.resolve_inst`) when building the typeclass-context
list for an `XMu` binder whose body uses a parametric instance
(`has_stream_t {| has_stream a |}` from `Network.TTCan.Prim.Clocked`).
The displayed shallow types are equal, so the discriminator is an
implicit typeclass dictionary the printer collapses.

This blocks all of `Network.TTCan.Impl.States` (every state machine
needs a `Clocked.t ntu` clocked-stream input fed through `let rec`)
and therefore `Network.TTCan.Impl.Controller`. **The fix is in the
lifter, not in source-level workarounds.**

## B. Lifter / typeclass interaction: refined-return-type instances

**Gap.** `S32R.s32r 7` returns `s: t b { v s == 7 }`. The
`has_stream_S32R` instance is on `t b`. The refined return type
doesn't trigger instance resolution, and inlining the value into a
`#lang-pipit` stream body fails. Lifting it to a top-level constant
(`let msc_max: message_status_counter = S32R.s32r 7`) hangs the
elaborator (typeclass resolution loops > 2 min).

**Workaround.** None yet. `Network.TTCan.Impl.Errors.scheduling_error_1`
is the only call site so far; left as a TODO in that module's body.
