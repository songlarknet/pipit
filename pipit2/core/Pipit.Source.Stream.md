# `Pipit.Source.Stream` — design notes

Shadow commentary for [Pipit.Source.Stream.fst](Pipit.Source.Stream.fst): a
Sugar-style source layer over the core stream terms.

## The `stream` builder

A `stream ts` is a *builder* for a stream tuple of (object-level) types `ts:
list typ`: a computation that, given a fresh-name counter, emits a width-`|ts|`
`tterm` and the next counter. The type vector `ts` is phantom — it never appears
in the emitted term except as the binder annotations `let'` / `mu` / `node`
recover from it — but it disciplines how the combinators compose. Width-1
streams are `stream [a]`; wider streams carry several components and are built /
taken apart with `zips` / `unzips` (and the fixed-arity sugar `zip2` / `unzip2` /
...). A later `check` / `infer` pass reconciles the two worlds.

The representation is a plain function, i.e. *reducible*: lowering / checking can
`norm` a `stream` down to a concrete `tterm`. Free `SVar`s are allocated with a
monotone counter and eliminated by the core's `close`, mirroring Pipit 1's Sugar
layer (fresh-name monad + `close`).

## Meta-unwrap: keeping pointwise expressions flat

Reading the components back out of a stream term is `components ts t n`: it
*meta-unwraps* a plain `TTuple es` back to its component `sterm`s (no wrapper, no
fresh name), and otherwise (a node output `TStreamApp ..`, a `TLet ..`, the
genuine tuple cases) binds the whole term to `|ts|` fresh variables with a single
`TLet ts t ..` and returns the projected `SVar` references plus that binding as
the wrapper. This keeps ordinary pointwise expressions flat and only genuine
tuples pay a `TLet`. `atomize` is the width-1 specialisation (a single `sterm`),
kept for `fby`; `components` never indexes a specific position — its result is
always consumed whole (`SPureApp` / `TStreamApp` / `TTuple`) or split by
`zips` / `unzips` — so no length refinement is needed.

## Combinators

- `fresh` / `fresh_vars` / `close_vars` — allocate one fresh named var; allocate
  one per type in a vector; close a list of vars at successive de Bruijn indices
  (`SVar x_i -> SBVar (k+i)`). The last two carry the width-`|ts|` builders.
- `fvar` / `const` — refer to an existing free var as a width-1 stream; a
  constant stream holding a pure value.
- `fby` — `v fby s`: `v` on the first instant, then the previous value of `s`
  (inherently width-1, so it uses `atomize`).
- `liftP` — pointwise lifting of a primitive head over a stream of its arguments:
  `liftP add (zip2 x y)`. A unary application needs no zip (`liftP not x`). It
  reads the argument components with `components`, applies `SPureApp p es`, and
  installs any bindings the reduction needed. The primitive's typing is checked
  later by `infer`; the tags are phantom.
- `zips` / `unzips` — the general (append / split) tuple combinators.
  `zips x y : stream (xs @ ys)` concatenates two stream tuples; `unzips #xs #ys :
  stream (xs @ ys) -> stream xs & stream ys` splits at `|xs|` via `splitAt`. Each
  projection of `unzips` re-emits its source, so a non-tuple source (a node
  output) is *duplicated* — the structural sharing a later CSE pass recovers.
- `zip2` / `zip3` / `unzip2` / `unzip3` — fixed-arity sugar over `zips` /
  `unzips`. `zip2 (x: stream [a]) (y: stream b) : stream (a :: b)` conses a
  width-1 head onto a tail (since `[a] @ b` reduces to `a :: b`); `unzip2`
  is its inverse, and the `3` variants nest one more.
- `let'` — non-recursive shared binding. `f` is applied to a *single* fresh tuple
  of variables (one per type in `a`), so every use of the bound stream shares one
  `TLet a` binder and the rhs is emitted once (no HOAS duplication). Multi-stream
  binding is `let' (zip2 x y) (fun xy -> let (sx, sy) = unzip2 xy in ..)`.
- `mu` — n-ary mutual recursion `xs = f xs`, built directly as the core's `TRec`
  over a group of `|a|` equations, each in scope of the whole group (`mu #[t1;
  t2] f` is a two-member mutual group).
- `letrec` — a recursive definition shared into a continuation (`let' (mu f)`).
- `node` — node instantiation: emit `head`'s result tuple `TStreamApp head es`
  applied to the argument components, `node #args #results head (s: stream args) :
  stream results`. A multi-output node is split with `unzip2` / `unzips`:
  `let (o1, o2) = unzip2 (node head (zip2 x y))`. Because each `unzip` projection
  re-emits the application, the node call is duplicated across the outputs and a
  later CSE pass (see [Pipit.Exp.Anf.md](Pipit.Exp.Anf.md)) hoists it into one
  binding.
- `exp_of_stream` — emit the underlying stream term, allocating fresh names
  from 0.

## Still to land (gated on a core extension)

- a CSE / sharing-recovery pass to hoist the `TStreamApp` that a multi-output
  `node` + `unzip` duplicates across its outputs into a single shared binding
  (now provided by [Pipit.Exp.Anf.fst](Pipit.Exp.Anf.fst)).
