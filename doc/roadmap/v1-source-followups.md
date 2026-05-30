# Version 1: source frontend follow-ups

Surface-language items uncovered while pruning the legacy code in
preparation for the IR-frontend. Listed roughly in order of expected
effort; none of these are blockers for IR design.

## Plugin / preprocessor

### `[@@proof_induct1]` ignores static parameters
The synthesised `__check_<id>` decl in
`Pipit_Plugin_Preprocess.mk_check_induct1_decl` assumes the spliced
`__core_<id>` has type `exp _ _ _`. When the source function has any
non-stream parameters the splice has type `p1: t1 -> … -> exp _ _ _`,
so `system_of_exp __core_<id>` fails with `Error 189`.

Fix: rewrite `mk_check_induct1_decl` to scan the static-parameter
prefix of `pat` and emit

```fst
let __check_<id> (p1: t1) … (pn: tn) =
  assert (induct1 (system_of_exp (__core_<id> p1 … pn))) by …;
  bless (__core_<id> p1 … pn)
```

Already verified separately that the lift itself handles static params
(scalar, refined, implicit `#_`, function-typed, and record-typed) and
their call sites. Only the proof wrapper is missing.

### `proof_induct k` for `k > 1`
`Pipit_Plugin_Attributes` only knows about `proof_induct1`. To revive
`example/Fir.Check.bibo3` (and unblock the TTCAN port, which already
uses `system_induct_k1` only) we'd add a `proof_induct k` attribute and
a `mk_check_induct_k_decl` that calls a `system_induct_k` helper.

### Generalise to contracts
`Pipit.Sugar.Contract` was deleted in the v0 cleanup. The TTCAN port
needs a `{rely; guar; body}` triple at the surface. Could be a single
attribute `[@@proof_contract_induct1]` synthesising
`Contract.contract_of_stream1` + `Contract.system_induct_k1` +
`Contract.stream_of_contract1`, mirroring the deleted code's shape.

### Top-level `let rec` doesn't strip `stream` annotations
`Pipit_Plugin_Preprocess.pre_decl` matches `TopLevelLet (Rec, _)` with
a literal `TODO` and passes the decl through unchanged. Users hit
"Identifier not found: stream" the moment they try to write a recursive
top-level helper with a `stream T` annotation in scope. Either erase
`stream` from those decls too, or diagnose the case cleanly.

### `lemma_pattern` surface
TTCAN injects SMT patterns from inside a `rec'` body using a
`lemma_pattern` ghost-stream effect (see
`example/ttcan/Network.TTCan.TriggerTimely.fst` line 168). Provide a
plugin-recognised surface combinator for this.

## Out of scope for v1

* FirN-style list-recursion building a Pipit expression — see the
  comment block in `example/Example.Fir.Check.fst`. Likely subsumed by
  the IR frontend itself.
* Mutual recursion across top-level stream functions.
