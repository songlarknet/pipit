# MasterModes lifter-explosion bisection

Self-contained reproduction of the apparent SMT/lifter explosion seen
when checking `Network.TTCan.Impl.States.master_modes` and (worse)
`tx_ref_messages`. See TTCAN notes in `example/ttcan/readme.md` and
git history for detailed analysis and prior workarounds.

These files are deliberately **not** built by `make verify` in
`pipit/plugin-test/`. V1 alone is ~2.5 min; V2b and V2c blow up the
F* process (≥ 6 GB RSS, never observed to finish).

## Layout

| File | Description |
| ---- | ----------- |
| `Plugin.Test.Bug.MasterModes.Types.fst` | Synthetic dependency surface (enums, `option` `has_stream`, refined-int instance, static `config` carriers). |
| `Plugin.Test.Bug.MasterModes.V0.fst`    | Baseline: `let rec _ = fby _` skeleton + outer-if only. |
| `Plugin.Test.Bug.MasterModes.V1.fst`    | + full nested if/else chain (no `Clocked`/`option`). |
| `Plugin.Test.Bug.MasterModes.V2a.fst`   | + `Some?` on `stream (option _)`. |
| `Plugin.Test.Bug.MasterModes.V2b.fst`   | + `ref_msg = Some master_idx` equality (plain int). |
| `Plugin.Test.Bug.MasterModes.V2c.fst`   | V2b but `master_idx` is a refined int. |

## How to time individual variants

From `pipit/plugin-test/`:

```sh
# Manually include this folder for one build.
PIPIT_DIR=.. ROOT_DIR=../.. \
FSTAR_INC_DIRS="base core rts/fstar abstract extract plugin/fst plugin/_build/default source" \
FSTAR_SRC_DIRS="bug-reproductions" \
COMPONENT=plugin-test-bug-repro \
make -f Makefile -j1 \
  ../../_build/cache/Plugin.Test.Bug.MasterModes.V0.fst.checked
```

Or, simpler, just hand-invoke `fstar.exe` once the dependencies are
already cached (which they are if you have run `make verify` for
`plugin-test/` recently):

```sh
/usr/bin/time -p ../../_opam/bin/fstar.exe \
  $(for d in base core rts/fstar abstract extract plugin/fst plugin/_build/default source plugin-test; \
      do printf -- '--include ../%s ' $d; done) \
  --cache_dir ../../_build/cache \
  --cache_checked_modules \
  --already_cached Prims,FStar,LowStar, \
  --warn_error -249 \
  bug-reproductions/Plugin.Test.Bug.MasterModes.V0.fst
```

## Recorded measurements (2026-06-04, macOS, M-series)

| Variant | Wall time | fstar RSS peak | Z3 behaviour          |
| ------- | --------- | -------------- | --------------------- |
| V0      |  14.8 s   | ~ 0.15 GB      | finishes              |
| V1      |   147 s   | ~ 3.4 GB       | one query at 99 % CPU |
| V2a     |   202 s   | ~ 2.4 GB       | one query at 99 % CPU |
| V2b     | killed*   | 5.9 GB at 1 m  | one query at 99 % CPU |
| V2c     | killed*   | 6.9 GB at 4 m+ | one query at 99 % CPU |

`*` killed after several minutes with no end in sight; fstar memory
monotonically growing.
