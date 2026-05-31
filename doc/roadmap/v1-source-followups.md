# Source-frontend roadmap

Surface-language follow-ups for the `#lang-pipit` source plugin
(`pipit/source/` + `pipit/plugin/`). Grouped by expected timeframe.
File and symbol references point at the current `amos/20260530-extract`
shape.

The driving consumer is the TTCAN port under `example/ttcan/`, which
was written against the now-deleted `Pipit.Sugar.{Shallow,Check,Contract}`
hierarchy and currently doesn't build (see `example/readme.md` and the
2026-05-24 TTCAN entry in `/memories/repo/tooling-notes.md`). Reviving
it is the working benchmark for "v1 source frontend complete".

## Short-term

### Contract support

The biggest single TTCAN blocker. `Pipit.Sugar.Contract` was deleted in
the v0 cleanup; the port still wants a `{rely; guar; body}` triple at
the surface. The deleted shape, still visible in
`example/ttcan/Network.TTCan.TriggerTimely.fst` (lines 178–198) and in
the commented stub in `example/ttcan/Network.TTCan.Impl.Triggers.fst`
(lines 211–237), was:

```fst
let c = Contract.contract_of_stream1 {
  rely = …_core;
  guar = …_core;
  body = …_core;
} in
assert (Contract.system_induct_k1 c) by (T.pipit_simplify_products []);
Contract.stream_of_contract1 c
```

**Chosen surface syntax: F\* effect form.**

```fst
[@@proof_induct1]
let mul_underapprox (a b: stream int): Stream int
  (requires true)
  (ensures (fun r -> a = 0 && b = 0 ==>^ r = 0)) =
  a * b
```

Implementation sketch: `Stream` is a placeholder effect (a degenerate
`Pure` alias) in `Pipit.Source`, with rely/guar carried as effect
indices. The reflecter sees the let-binding's computation type, peels
off `Stream a (requires R) (ensures G)`, and dispatches into the
contract layer — verified to parse and typecheck cleanly:

```fst
effect Stream (a: Type) (rely: stream bool) (guar: stream a -> stream bool) =
  Pure (stream a) (requires True) (ensures (fun _ -> True))
```

Naming follows Pulse's `stt` (type) / `STT` (effect) precedent: lowercase
`stream a` is the value type used in parameter and trivial return
positions; uppercase `Stream a (requires R) (ensures G)` is the
effect form used in return position when the binding has a contract.
This is the same split as F\*'s `Tot a` / `Pure a (...)(...)` —
the simplified ("no annotations") form is what users write by
default, and the annotated form is reserved for contracted bindings.

Key properties:

* The existing `[@@proof_induct1]` (and the planned `proof_induct k` /
  `proof_induct0`) annotations are reused literally. The plugin
  dispatches via the contract path when the let-binding's computation
  has `Stream` as the effect head.
* The body is just `a * b` — a normal stream expression. No
  restriction on body shape; leading `let`s, conditionals, helper
  bindings all work because the contract lives in the type, not in
  the body.
* `guar`'s `r` is `stream a`, type inferred from the effect index.
  Referring to `pre r` or other streaming combinators inside `guar`
  is fine — the guarantee is a stream property that holds at every
  step.
* Inputs stay lowercase `stream T` (effects are illegal in parameter
  positions — F\* Error 187).

**Caveat to verify at implementation time:** F\* effect indices are
sometimes restricted to ground types. The sketch above uses
`stream bool` / `stream a -> stream bool` as indices; if that bites,
the fallback is to use plain `bool` / `a -> bool` indices and treat
the lift to stream-level as a plugin-only concern. Worth a five-line
test before committing the design.

Plumbing: the existing `[@@proof_induct1]` attribute is reused as-is
— the plugin dispatches on the let-binding's computation type and,
when it sees `Stream a (requires R) (ensures G)`, synthesises the
analogue of the deleted `Contract.contract_of_stream1` +
`Contract.system_induct_k1` + `Contract.stream_of_contract1`
instead of the plain `system_induct_k1` path. Mid-term this
generalises naturally to `proof_induct k` for k > 1 alongside the
standalone `proof_induct k` work below — same attribute, same
dispatch rule.

A re-introduced contracts layer is also the prerequisite for the
*long-term* modular extraction story (one C entry point per contract,
verified against `rely`/`guar`, called from neighbouring contracts).

### `proof_induct k` for k > 1, and a less misleading name for k = 0

`Pipit_Plugin_Attributes` only knows `proof_induct1`. Two related
extensions:

* **`proof_induct k`** (k > 1) — generalise `mk_check_induct1_decl` in
  `pipit/plugin/Pipit_Plugin_Preprocess.ml` to call a
  `system_induct_k` helper and emit the corresponding obligation.
  Concrete consumer: `example/Example.Fir.Check.fst` `bibo3` (commented
  block at lines 38–63), where the three-tap FIR's two-deep state needs
  2-induction.
* **`proof_induct0`** — currently absent. Despite the name, `k = 0`
  isn't *inductive*: it just discharges the property as an invariant
  with no step-case strengthening. Wanted as an explicit annotation
  because users frequently reach for "no induction needed, just check
  it" and currently have to fall back to writing a vanilla F* lemma
  next to the spliced core. Pick a name that doesn't suggest induction
  — candidates: `proof_invariant`, `proof_check`, `proof_safety`.

**TTCAN does not need `proof_induct k > 1`.** The existing roadmap
copy claimed it did; it was wrong. Both active uses in
`Network.TTCan.TriggerTimely.fst` (`count_when_checked` line 143,
`trigger_fetch_checked` line 197) are `system_induct_k1`. `proof_induct
k` is for `bibo3` only.

### `[@@proof_induct1]` (and friends) over static parameters

The synthesised `__check_<id>` decl in
`Pipit_Plugin_Preprocess.mk_check_induct1_decl` assumes the spliced
`__core_<id>` has type `exp _ _ _`. When the source function has any
non-stream parameters the splice has type `p1: t1 → … → exp _ _ _`,
so `system_of_exp __core_<id>` fails with F\* `Error 189`.

Fix: scan the static-parameter prefix of `pat` and emit

```fst
let __check_<id> (p1: t1) … (pn: tn) =
  assert (induct1 (system_of_exp (__core_<id> p1 … pn))) by …;
  bless (__core_<id> p1 … pn)
```

The lift itself already handles static params (scalar, refined,
implicit `#_`, function-typed, and record-typed) — only the proof
wrapper is missing.

**TTCAN does need this.** `trigger_index` in
`Network.TTCan.TriggerTimely.fst` (line 162) takes a `(cfg: config)`
and `(c: cycle)` as static params and is wrapped in a checked
contract — exactly the shape that currently trips Error 189. Same
story for the would-be `prefetch_core_contract` stub in
`Network.TTCan.Impl.Triggers.fst`.

The wrapper extension is shared with `proof_induct k` and the
contract-effect dispatch above; doing it once covers all three uses
of the same attribute family.

### Lemma combinator (`lemma_pattern` and friends)

TTCAN currently injects SMT patterns from inside a `rec'` body using a
`lemma_pattern` ghost-stream effect — see
`example/ttcan/Network.TTCan.TriggerTimely.fst` line 168 (call site)
and lines 105–117 (the pattern lemma it points at). The original
design had two reasons:

1. Work with the existing shallow-lift syntactic sugar without breaking
   the streaming abstraction.
2. Carry preconditions that aren't available when the core expression
   is constructed (so a plain F\* `Lemma` doesn't fire).

Reason (1) is largely obsolete with the plugin pipeline — bodies are
ordinary F\* terms during lifting. Reason (2) still holds: a checked
property may depend on context that the core builder doesn't see.

Concrete work: a plugin-recognised surface combinator (call it
`lemma`, `assume_pattern`, or similar) that lifts to a no-op at the
core level but injects an SMT pattern at the proof level. Likely the
cleanest design lands alongside contracts — the pattern can be scoped
to a `rely`/`guar` obligation. Worth a fresh design pass before
re-implementing the old shape.

### Top-level `let rec` doesn't strip `stream` annotations

`Pipit_Plugin_Preprocess.pre_decl` matches `TopLevelLet (Rec, _)` with
a literal `TODO` and passes the decl through unchanged. Users hit
"Identifier not found: stream" the moment they try to write a
recursive top-level helper with a `stream T` annotation in scope.
Either erase `stream` from those decls too, or diagnose the case
cleanly. Adjacent: local `let rec` (`Tv_Let true`) inside a streaming
body is also unsupported — currently only `rec'` works — and blocks
`Plugin.Test.Core.Basic.eg_letrecfun`.

## Mid-term

### CSE on the core expression, with `[@@proof_no_cse]` opt-out

Several existing examples currently need users to manually pull out
shared subexpressions so that contract obligations refer to the same
core binding:

* `example/Example.Pump.Check.fst` lines 99–115
  (`spec_any_needs_extra_invariant_manual_cse`) hand-extracts
  `sol_try_c` / `level_low_c` to make 1-induction discharge.
* `example/ttcan/Network.TTCan.TriggerTimely.fst` lines 169–174 has
  a commented-out `sofar (time_increasing now) ==> …` check that
  cannot be proved precisely because the `sofar`'s internal state is
  a different binding than the one inside the contract body — the
  comment block names CSE as the fix.

`Pipit.Tactics.Cse` already exists (with `pipit/test/Pipit.Tactics.Cse.Test.fst`)
as the building block. The mid-term work is:

1. Run CSE as a default postprocess step on every spliced core.
2. Add a `[@@proof_no_cse]` per-binding (or per-module) opt-out for
   diagnosis and for the rare cases where CSE confuses an induction
   obligation.

### Multi-arm `match` on stream scrutinees

`Pipit.Source.Ast.AMatch` currently only handles `AppPureConst`
(static scrutinee); `AppPureStream` is deferred. This blocks
`Plugin.Test.Core.Match.eg_streaming_match_option` (commented at
lines 28–36) and the broader general-pattern story noted in the
2026-05-30 memo. Until then users get `if/then/else` over `bool`
plus the irrefutable single-arm destructure that landed in commit
701884b.

### Mutual recursion across top-level stream functions

Today each top-level streaming let is lifted independently; mutually
recursive `let … and …` groups would need the splice plugin to lift
the whole group together (or co-resolve their core names before
lifting). No TTCAN blocker, but on the path to richer specs.

## Long-term

### Separate compilation and extraction

Contracts give modular *verification* — the rely/guar boundary means
a callsite need only see the contract, not the body. The matching
extraction story is missing: today each `*.Extract.fst` module bundles
its full spliced core into a single KaRaMeL run and the C output is
monolithic. Long-term we want one C entry point per contract,
verified against its rely/guar, called by neighbouring contracts
without re-extracting their bodies. Prerequisite: short-term contract
support.

We probably want finer-grained modular extraction than per-contract,
though. Sketch: add a core constructor that annotates a sub-`exp` with
a pre-translated executable system, e.g.

```fst
XExtracted : sys: <executable system> -> e: exp 't c a { sys ≈ e } -> exp 't c a
```

with `cexp` requiring `sys == e` semantically (the existing
`state_of_exp` / `system_of_exp` translation gives the equivalence;
the constructor just lets us *cache* one branch of it). The splice
pipeline would then lift each `XExtracted`'s `sys` payload up to a
top-level name and emit a call at the use site, rather than
re-translating the inner `exp` every time. This is what would let
modular extraction work at arbitrary sub-expression granularity
without going via a full contract boundary.

Likely needs a lower-level Pulse system definition exposed to the
core layer (today `Pipit.Exec.Pulse.mk_reset` / `mk_step` are
synthesised at the splice site over a complete `esystem`; an
extracted sub-expression would want to point at a pre-existing
Pulse `fn` instead). Details still TBD — record here so the design
constraint isn't lost.

### Meta-specialisation / staged inputs

Specialise a stream function at a compile-time constant — e.g.
`fir [1; 2; 3] x` reduces to a concrete three-tap filter at splice
time, with the list fully unrolled. Subsumes the FirN-style
list-recursion blocker described in the comment block at
`example/Example.Fir.Check.fst` lines 65–66, and the manual unrolling
that the TTCAN trigger array uses today.

## Very long-term

### Automatic invariant discovery (applicative invariants)

Synthesise the strengthening invariant that turns a `proof_induct1`
obligation into something inductive without the user spelling it out.
The Pump `spec_any_needs_extra_invariant_manual_cse` case is the
canonical small instance — `countsecutive (x && y) <= countsecutive y`
should be discoverable.

### Counterexample generation

When a check fails, fall out of the SMT failure into a concrete input
trace (single-step bounded model checking against the lifted core).
Complements the proof side directly: every failed obligation already
carries the relevant binders and types.

### Iterative `proof_induct` search

Once `proof_induct k` is parameterised, the user-visible knob is `k`.
Iteratively try `k = 0, 1, …, n` until the obligation discharges (or
n is exhausted). Cheap to bolt onto the attribute-driven shape.

## Other gaps spotted while writing this

These didn't make the user's original list but came up during the
walk-through and are worth tracking somewhere:

* **Refinement preservation.** `Pipit.Source.Ast.Reflect.strip_refinements`
  currently drops every `Tv_Refine` predicate on types that flow into
  the intrinsically-typed core (memo entry 2026-05-29). Without it,
  TTCAN's `S32R.t {min = …; max = …}` and `index` refinements vanish
  at the boundary and have to be reasserted by hand. Proper support
  needs dependent `exp` typing — call it long-term, but at least
  document it.
* **`has_stream` derivation beyond single-constructor records.** Today
  the user must hand-write `instance has_stream_T = { ty_id; val_default }`
  for every TTCAN record (see lines 53–66 of
  `Network.TTCan.Impl.Triggers.fst` and equivalents in States/Controller).
  `derive_has_stream` covers the common case; auto-generating it for
  the `#lang-pipit` module preamble would remove ~50% of the surviving
  TTCAN boilerplate.
* **Diagnostics for splice failures.** Errors that surface from inside
  `Pipit_Plugin_Preprocess` (e.g. the Error 189 above) currently bubble
  up at the `%splice[]` line with no surface-level explanation. A
  one-line "while lifting `<name>`: static-param wrapper missing"
  preamble would save serious time, especially for the contract /
  induction-k follow-ups above where the same root cause manifests
  differently in each consumer.
* **Top-level extraction wrappers boilerplate.** The
  `example/ttcan/Network.TTCan.Extract.fst` Pulse migration carries a
  per-target `KRML_OPT += -warn-error -26` workaround (memo entry
  2026-05-24). Eventually want this kind of escape hatch documented or
  removed.

## Soundness (mostly not user-facing, but important)

A separate group. Most of these don't affect the surface language but
they weaken the meta-theory and should be re-proved before we call v1
done; one (the default-proof entry just below) *is* user-visible.
Companion to `doc/roadmap/v0-contracts-missing-proofs.md`, which
tracks the older contract-layer obligations.

### Unannotated bindings discharge no checks; need a default proof strategy

Today a top-level streaming `let` without a `[@@proof_…]` attribute
falls through `Pipit_Plugin_Preprocess.pre_decl` to the plain
lift-and-`bless` path with no obligation emitted at all. Any
`check "…" e` inside that body (or inside a function it calls) is
silently trusted — there is no Z3 query, no `system_induct_k1`
discharge, nothing. Combined with the `exp`-vs-`cexp` issue below,
this means the surface language has a real soundness gap for the
"forgot the attribute" case.

The intended shape:

* **Default** — every top-level streaming `let` runs an automatic
  proof attempt. Starting points to try, in increasing cost:
  `proof_noinduct` (≡ `proof_induct0`, just discharge the check as an
  invariant), then `proof_induct1`. The cheapest tier should be
  effectively free when the body contains no `check` at all — most
  combinator bindings — so the overhead lands on bindings that
  *should* be paying for a check anyway. Open question: how fast
  does the SMT call degrade when the body calls into helpers that
  do carry checks but none directly?
* **`[@@proof_defer]`** — opt out explicitly. The body may carry
  checks but the caller is responsible for discharging them. This is
  the right knob for contract-style reasoning where you want the
  body visible (no abstraction barrier) but the obligations float up
  to the contract boundary. Today the lack of this annotation is
  exactly what forces the "no attribute = trust me" default; making
  the silent path explicit closes the soundness hole without
  forcing every helper to spell out `proof_noinduct`.
* **Explicit annotations stay as today** — `proof_induct1`,
  `proof_induct k`, etc. override the default and continue to mean
  what they currently mean. The same attributes also drive the
  contract-effect dispatch (Contract support entry above), so no
  new `proof_contract_*` family is needed.

Implementation pointers: `mk_check_induct1_decl` in
`pipit/plugin/Pipit_Plugin_Preprocess.ml` already shows the
splice-time structure for emitting a check obligation; the default
path needs the same scaffolding gated on a fresh
`Pipit_Plugin_Attributes` entry (`proof_default`, `proof_defer`).
Worth measuring on `make plugin-test` and `make example` before
flipping the default — the budget per spliced `let` should be tight
enough that turning it on for the whole tree isn't a tax.

Cross-references:

* `proof_induct k` for k > 1 and a less-misleading name for k = 0
  (short-term entry above) covers the picking-the-right-k axis.
* `[@@proof_induct1]` over static parameters (short-term entry
  above) is a prerequisite — the wrapper has to handle static-param
  prefixes before the default can apply uniformly.
* `New core generation emits exp, not cexp` (below) is the other
  half of the same hole: even with a default `proof_induct1`, the
  per-node `XCheck` obligations carried by `cexp` are still
  `bless`-ed away.

### New core generation emits `exp`, not `cexp`

The block comment at the top of `pipit/source/Pipit.Source.Ast.Lower.fst`
calls this out:

> `exp`, not `cexp`, for now — blessing to `cexp` is left to the
> splice site so that we can iterate on Lower without paying for
> `check_all` discharge on every change.

The splice plugin then wraps the result in `bless` (see
`Pipit_Plugin_Preprocess.mk_check_induct1_decl` lines 245–290, which
emits `assert (induct1 …) by …; bless __core_<id>`). That means the
*property* obligations carried by `cexp`'s sealed-ness are not
actually discharged on the freshly-lifted core — `bless` just claims
them. The old `Pipit.Sugar.Vanilla`/`Pipit.Sugar.Check` pipeline used
`cexp` throughout and discharged `check_all` at lift time.

Fix is structurally easy (have Lower emit `cexp` directly, lean on
the existing `Exp.Checked.*` infrastructure) but will slow per-splice
typechecking; deferred until the surface stabilises. Until then,
every `[@@proof_induct1]` discharges only the inductive obligation,
not the per-node `XCheck` validity that `cexp` would enforce.

### Abstract layer: 6 admits from the F* 2025-11-16 update

All marked `(* TODO:ADMIT:update to latest F* 20251116 *)`. They
worked before the F* dev-build bump and need re-proving against the
current normalizer / SMT encoding:

* `pipit/abstract/Pipit.System.Exp.Check.Contracts.fst` lines 148, 247.
* `pipit/abstract/Pipit.System.Ind.fst` line 144 (`induct_k` soundness,
  k = 2 case).
* `pipit/abstract/Pipit.System.Exp.Check.Obligations.fst` lines 134, 163.
* `pipit/abstract/Pipit.System.Exp.Check.Assumptions.fst` line 125.

Together these are the abstract-system step from `cexp`-checks-pass
to "the underlying transition system actually satisfies the check".
With them admitted, the k-induction story is sound *modulo these
specific cases* — none of them are believed to be false; they're all
proofs that were already there and broke on the update.

### Core layer: `cexp` preservation admits

Smaller and more local than the abstract-layer group:

* `pipit/core/Pipit.Exp.Checked.Compound.fst`
  * `close1` (line 55, `AXIOM:ADMIT`): closing a `cexp` over a fresh
    variable preserves validity. Comment says "Cannot yet prove this:
    used in the syntactic sugar, but not in the semantics."
  * `weaken` (line 65, `TODO:ADMIT`): context weakening preserves
    validity.
* `pipit/core/Pipit.Exp.Checked.Bless.fst` line 242
  (`TODO:ADMIT:update to latest F* 20251116`): same F* bump regression
  as the abstract layer.
* `pipit/core/Pipit.Exp.SimplifyLet.fst` line 92: `bigstep_simplify`
  (let-binding simplification preserves the big-step semantics) is a
  one-liner `admit ()`. The SimplifyLet pass is what the splice
  postprocess actually runs, so this is on the trusted path.

### Small bookkeeping admits

* `pipit/core/Pipit.Exp.Binding.fst` line 122 — local `assume
  (C.get_index c'' i' == a)`, marked `TODO PROVE EASY`.
* `pipit/base/Pipit.Context.Base.fst` line 31 — `admit ()`, marked
  `TODO PROVE EASY`.

### Intentional axioms (not bugs, but worth listing)

For the record so they don't get accidentally "fixed":

* `pipit/core/Pipit.Prim.Shallow.fst` `axiom_var_eq` (line 60) and
  `axiom_prim_eq` (line 68): the front-end's contract that types /
  primitives with the same identifier are equal. These are real
  axioms — the encoding can't prove them and shouldn't try.
* `pipit/source/Pipit.Source.fst` `assume val fby` / `assume val check`
  and `pipit/plugin/fst/Pipit.Plugin.Interface.fst` `assume val rec'`:
  surface combinators with no F\* semantics — they only exist to be
  rewritten by the splice plugin into their `core_lifted` counterparts.

## Explicitly out of scope for v1

* FirN-style list-recursion building a Pipit expression — see the
  comment block in `example/Example.Fir.Check.fst` lines 65–66.
  Subsumed by the meta-specialisation work above (long-term).
* Mutual recursion across top-level stream functions, beyond the
  mid-term entry above.
* General pattern matches that bind new variables on streaming
  scrutinees (commented-out `eg_streaming_match_bind` in
  `Plugin.Test.Core.Match.fst`). The mid-term multi-arm-match item
  unblocks ctor/record/tuple destructure; binding new stream-typed
  variables is a separate design.
