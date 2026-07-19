# `Pipit.Example.Bool` — design notes

Shadow commentary for [Pipit.Example.Bool.fst](Pipit.Example.Bool.fst): a
concrete boolean signature environment and a first rewrite rule.

This instantiates the syntactic core at a tiny value universe (one type, `bool`)
with a handful of named primitives (plus one two-output node, `ctrl`), and
defines `sofar_and` — the deliberately gentle temporal rewrite from the roadmap
([../doc/roadmap/next-project-plan.md](../doc/roadmap/next-project-plan.md), M1'):

    sofar (a && b)  ~=  (sofar a) && (sofar b)

Two things replace the old `table`-based version:

- primitives now live in an *environment* (`benv`), keyed by name and carrying
  only signatures (no dynamic semantics); and
- the rule `step_sofar_and` matches fully *concrete* syntax (`PVar "sofar"`,
  `[_; _]`), so — unlike the old table-abstract `prim`, which extracted to
  `Obj.t` and could not be matched in OCaml — it now extracts to honest native
  OCaml.

The rule is unverified: its soundness (`stream_eq` between the two sides) is
deferred to the congruence / rule-lemma machinery.

## Contents

- `bool_ty` — the one object-level value type, booleans.
- `p_and` / `p_or` / `p_not` / `p_sofar` — primitive heads (pure terms in
  operator position); `p_sofar` is a unary temporal operator ("has held at every
  instant so far"), the rest are the usual boolean connectives.
- `benv` — the boolean signature environment: the connectives and the unary
  temporal `sofar` as primitives over `bool`, plus a two-input, two-output node
  `ctrl` (the ex-tuple calling convention). Carries only signatures; first-order
  assoc lists (`L.assoc name` resolves a head).
- `step_sofar_and` — the rewrite rule as a local `step`: push `sofar` through
  `&&`, identity on every other shape, so
  `Pipit.Transform.Rewrite.rewrite step_sofar_and` fires it at every
  `sofar (_ && _)` in a term, including under binders.
