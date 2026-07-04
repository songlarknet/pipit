# Pipit examples

## Time-triggered Controller Area Network (medium)

TTCAN is a time-triggered network architecture used in the automotive industry.
The time-triggered network has a static schedule which all nodes must
statically agree on. We implement the high-level driver logic, for which we can
generate C, and prove some properties about an abstraction.
[The readme has more information.](ttcan/readme.md)

The TTCAN example lives under [`ttcan/`](ttcan/) and now uses the
`#lang-pipit` plugin pipeline.

## Smaller examples

The small examples use the `#lang-pipit` plugin pipeline:

- [Pump](Example.Pump.Check.fst) — a controller for a water reservoir. There
  is a video of the controller in action on
  [YouTube](https://youtu.be/6IybbQFPOl8). Extraction:
  [Example.Pump.Extract](Example.Pump.Extract.fst).
- [Simple](Example.Simple.Check.fst) — a collection of one-liner stream
  functions with small properties. Extraction:
  [Example.Simple.Extract](Example.Simple.Extract.fst).
- [Fir](Example.Fir.Check.fst) — a small BIBO proof for a two-tap FIR
  filter, plus commented-out sketches of `bibo3` (needs `proof_induct k`
  for k>1) and `FirN` (needs a clean story for mixing F* list induction
  with stream proofs).

A minimal regression test for cross-function lifting lives alongside the
plugin tests as
[Plugin.Test.Bug.Crossfunction](../pipit/plugin-test/Plugin.Test.Bug.Crossfunction.fst).

The legacy hand-written versions of Pump, Simple, and Fir (using the older
shallow-lift tactic and the `Pipit.Sugar.Vanilla` primitive table) have been
removed; the plugin versions cover the same ground with less boilerplate. The
history is in git if you need to compare.
