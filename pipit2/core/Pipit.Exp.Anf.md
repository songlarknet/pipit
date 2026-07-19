# `Pipit.Exp.Anf` — design notes

Shadow commentary for [Pipit.Exp.Anf.fst](Pipit.Exp.Anf.fst): an A-normal-form
core IR and the normalizing lowering from a `tterm`, with common-subexpression
elimination that recovers the sharing the shallow source layer loses.

## Why this exists

The source layer emits each output of a multi-output node call as its own
`TLet`-binding of the *same* `TStreamApp` — the projection idiom
`TLet tys (TStreamApp ..) (TTuple [SBVar i])` (see
[Pipit.Source.Stream.fst](Pipit.Source.Stream.fst) `node22`). Because a term is a
tree (not a DAG), that node-application subterm is *duplicated* wherever more
than one of its outputs is used. Sharing is recovered here by a *multi-output*
binding form, `CLetNode` (the `LetStreamApp` of the plan): lowering hoists each
*distinct* node instantiation into one `CLetNode` and rewrites its projections to
variable references. CSE is uniform — every binding is hash-consed against the
ones already emitted — so ordinary common subexpressions collapse too.

## de Bruijn *levels*, not indices

Unlike `sterm` (whose `SBVar` counts binders inward, innermost = 0), an ANF
`AVar` is a de Bruijn *level*: 0 is the *outermost* `CLet` / `CLetNode`. Levels
are what make the append-only telescope construction sound — emitting a new
binding never shifts the atoms already built, which is exactly what lets CSE
reuse an earlier binding's level. A consumer reads levels from the outside in.

## Scope

Full ANF (every `SPureApp` argument is named to an atom) over the first-order
fragment: `SPure`, `SBVar`, `SFby`, `SPureApp`, and the tuple formers `TTuple` /
`TStreamApp` / `TLet`. Recursion (the n-ary `TRec` group) is deferred — faithful
recursive ANF wants the register / transition-system view — so the lowering is
partial (`option`) and returns `None` on `TRec` (and on free `SVar`s).

## ANF syntax

- `atom` — a trivial operand: a bound stream `AVar` (by de Bruijn *level*) or a
  constant pure value `APure`. `APure` subsumes literals, so there is no separate
  atom for those.
- `rhs` — the right-hand side of a single-output binding: `RFby` (a delay) or
  `RPureApp` (a single-output primitive / operator application), both over
  already-named atoms.
- `cont` — an A-normal continuation. `CLet` binds one flow; `CLetNode`
  instantiates a node once and binds its (list of) output flows; `CRet` is the
  tail, returning the term's output flows (a list, for multi-output node bodies).
  The `list typ` on `CLetNode` is the node's output types (all streams, so a
  plain type list suffices — no binder kind needed).

## Lowering state (an append-only, hash-consed telescope)

- `binding` — one emitted binding, paired (via `width`) with the number of output
  flows it binds: a `BLet` binds 1, a `BNode` binds one per output type.
- `state { binds; next }` — the telescope built so far (outermost binding first)
  and the next free level (= total width emitted).
- `find_level` — the base level of the first binding structurally equal to the
  target, or `None`; `acc` is the running level (each binding advances it by its
  width).
- `emit` — hash-consing: reuse an existing structurally-equal binding's base
  level (CSE), else append and return its fresh base level.

## Lowering `sterm` → ANF

- `proj_atoms base tys` — the projection atoms of a node call bound at base level
  `base`: `[AVar base; AVar (base+1); ..]`, one per result type. Needs an
  explicit `decreases tys` (base increases, so the term metric is on `tys`).
- `zip_at` — pair up already-lowered atoms with their types for `senv` extension.
- `lower` / `lower_t` / `lower_list` — `senv` maps a source de-Bruijn *index* to
  the ANF atom (and type) it lowered to; `st` is the telescope. Each call returns
  the updated telescope, the atom(s) naming the output(s), and the type(s).
  Partial: `None` on the deferred / ill-formed cases (`SVar`, `TRec`, a bare /
  ill-typed node). The source `TLet` is *inlined* into `senv` — only its `rhs`'s
  own bindings persist; the let itself emits no binding.
- `build_cont` — fold the finished telescope (outermost first) into nested lets
  over the tail atoms.
- `to_anf` — lower a closed, recursion-free `tterm` to ANF, or `None` if out of
  scope.

Types flow from annotations throughout (`SFby`'s init via `infer_val`,
`env.prims` results, `nodety.results`) — there is no separate inference pass.
