# `Pipit.Source.Stream` — design notes

Shadow commentary for [Pipit.Source.Stream.fst](Pipit.Source.Stream.fst): a
Sugar-style source layer over the core stream terms.

## The `stream` builder

A `stream a` is a *builder* for a stream term of (object-level) type `a`: a
computation that, given a fresh-name counter, emits a (width-1) `tterm` and the
next counter. The result-type tag `a: typ` is phantom — it never appears in the
emitted term except as the binder annotations `let'` / `mu` recover from it — but
it disciplines how the combinators compose. A later `check` / `infer` pass
reconciles the two worlds.

The representation is a plain function, i.e. *reducible*: lowering / checking can
`norm` a `stream` down to a concrete `tterm`. Free `SVar`s are allocated with a
monotone counter and eliminated by the core's `close`, mirroring Pipit 1's Sugar
layer (fresh-name monad + `close`).

## Meta-unwrap: keeping pointwise expressions flat

A stream is represented as a width-1 `tterm`; the pointwise combinators
*meta-unwrap* a plain `TTuple [e]` back to the single `sterm` `e` (via `atomize`),
so ordinary expressions stay flat and only genuine tuples (node outputs) pay a
`TLet`. `atomize`'s fast path inlines `TTuple [e]` with no wrapper and no fresh
name; otherwise (a node output `TLet ..`, the one genuine tuple case) it binds
the term to a fresh variable so the operand becomes a variable reference and the
returned wrapper is the enclosing `TLet`.

## Combinators

- `fresh` / `fvar` / `const` — allocate a fresh named var; refer to an existing
  free var; a constant stream holding a pure value.
- `fby`, `liftP1`, `liftP2` — `v fby s`, and lifting unary / binary primitive
  heads pointwise over streams. The primitive's typing is checked later by
  `infer` against the signature environment; the tags are phantom.
- `let'` — non-recursive shared binding. `f` is applied to a *single* fresh
  variable, so every use of the bound stream shares one `TLet` binder and the
  rhs is emitted once (no HOAS duplication). A single-stream let is the n = 1
  tuple let.
- `mu` — single-stream recursion `x = f x`, built as the n = 1 case of the core's
  n-ary `TRec` (a one-member group).
- `letrec1` — a recursive definition shared into a continuation (`let' (mu f)`).
- `node22` — multi-output node instantiation (representative fixed arity: 2
  stream inputs, 2 outputs), returning an F* tuple of output streams so the
  caller can `let (o1, o2) = node22 head s1 s2 in ..`. Each output is its own
  `TLet [o1; o2] (TStreamApp head [e1; e2]) (TTuple [SBVar i])` binding the *same*
  application; because a term is a tree (not a DAG) that application is duplicated
  across the two outputs, and a later CSE pass (see
  [Pipit.Exp.Anf.md](Pipit.Exp.Anf.md)) hoists it into one binding.

  **Node arguments MUST be atoms** — counter-stable references such as `fvar` /
  `const` that allocate no fresh names — since they are re-emitted under each
  output; a non-atom would allocate divergent fresh names in the two copies and
  break both the sharing CSE recovers and the single-instantiation meaning. Bind
  non-atomic arguments with `let'` first.
- `exp_of_stream` — emit the underlying stream term, allocating fresh names
  from 0.

## Still to land (gated on a core extension)

- `letrec2` / mutual recursion needs an n-ary source combinator over `TRec` (the
  single-stream `mu` is the n = 1 case);
- a CSE / sharing-recovery pass to hoist the `TStreamApp` that `node22`
  duplicates across its two outputs into a single shared binding (now provided by
  [Pipit.Exp.Anf.fst](Pipit.Exp.Anf.fst)).
