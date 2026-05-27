# Pipit examples

## Time-triggered Controller Area Network (medium)

TTCAN is a time-triggered network architecture used in the automotive industry.
The time-triggered network has a static schedule which all nodes must
statically agree on. We implement the high-level driver logic, for which we can
generate C, and prove some properties about an abstraction.
[The readme has more information.](ttcan/readme.md)

The TTCAN example lives under [`ttcan/`](ttcan/) and currently uses the older
shallow-lift tactic (`Pipit.Sugar.Shallow.Tactics.Lift`). It is temporarily
disabled while a pre-existing tactic failure in `Network.TTCan.TriggerTimely`
(`tac_break_binder` stubbed during the F* migration) is being resolved.
Re-enabling will likely coincide with porting it to the `#lang-pipit` plugin
pipeline.

## Smaller examples (under `pipit/plugin-test/`)

The small examples — `Pump`, `Simple`, and a few bug reproducers — now live in
the plugin-test directory and are written using the `#lang-pipit` front-end:

- [Pump](../pipit/plugin-test/Plugin.Test.Example.Pump.Check.fst) — a
  controller for a water reservoir. There is a video of the controller in
  action on [YouTube](https://youtu.be/6IybbQFPOl8). Extraction:
  [Plugin.Test.Example.Pump.Extract](../pipit/plugin-test/Plugin.Test.Example.Pump.Extract.fst).
- [Simple](../pipit/plugin-test/Plugin.Test.Example.Simple.Check.fst) — a
  collection of one-liner stream functions with small properties. Extraction:
  [Plugin.Test.Example.Simple.Extract](../pipit/plugin-test/Plugin.Test.Example.Simple.Extract.fst).
- [Bug.Crossfunction](../pipit/plugin-test/Plugin.Test.Example.Bug.Crossfunction.fst) —
  a minimal regression test.

The legacy hand-written versions of Pump, Simple, and Fir (using the older
shallow-lift tactic and the `Pipit.Sugar.Vanilla` primitive table) have been
removed; the plugin versions cover the same ground with less boilerplate. The
history is in git if you need to compare.
