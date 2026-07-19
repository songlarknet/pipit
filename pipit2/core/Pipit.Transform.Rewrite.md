# `Pipit.Transform.Rewrite` — design notes

Shadow commentary for [Pipit.Transform.Rewrite.fst](Pipit.Transform.Rewrite.fst):
an unverified, environment-free rewrite driver.

This is the "untrusted transform" half of the story (see
[../doc/roadmap/next-project-plan.md](../doc/roadmap/next-project-plan.md),
milestone M1'): a driver applies a local `step` at every node and produces a new
`sterm`. It carries *no* soundness proof — establishing
`stream_eq e (rewrite step e)` is a separate obligation (per-rule congruence
lemmas, deferred). Being pure syntax → syntax, it needs *no* environment at all
(the checker needs signatures, the evaluator needs the dynamic interpretation,
the transform needs neither).

`rewrite step` is a single bottom-up pass: it rewrites every child first, then
applies `step` once at the (rebuilt) node. A `step` that only matches a fixed
shape and is the identity elsewhere therefore fires everywhere that shape occurs,
including under binders — exactly the congruence behaviour a rule-based optimiser
wants.

`rewrite` / `rewrite_args` act on single streams and never descend into a
`tterm`; `rewrite_t` traverses the tuple layer and calls back into `rewrite` at
the `sterm` leaves (tuple nodes carry no `step` of their own — the rule acts on
single streams).
