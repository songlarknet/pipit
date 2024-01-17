# Time-triggered CAN

This directory contains the time-triggered CAN implementation.

There are two main parts: the verified abstract trigger-scheduling, described in Section 2 of the paper, and the as-yet-unverified executable implementation.

## Verification

The [Network.TTCan.TriggerTimely module](Network.TTCan.TriggerTimely.fst) contains the verified trigger-scheduling.
There are a few superficial differences from the paper version: in particular, the syntax is a fair bit noisier, the names of some lemmas were changed, and the trigger array parameter was omitted from the paper.
We chose to simplify the syntax in the paper and show the planned future syntax rather than the current syntax.

The corresponding Kind2 verifications are in [lus/trigger_simple_enable.lus](lus/trigger_simple_enable.lus) and [lus/trigger_full_enable.lus](lus/trigger_full_enable.lus).

## Implementation

The implementation is divided into four main parts:
[Network.TTCan.Types](Network.TTCan.Types.fst) contains the high-level types; the `Network.TTCan.Impl.*` modules contain the actual Pipit code;
[Network.TTCan.Extract](Network.TTCan.Extract.fst) contains boilerplate and extraction options for generating C code; and the `Network.TTCan.Prim.*` modules contain mostly-boilerplate definitions of primitive operators (machine integers, bitvectors, etc).

There is currently a bit of boilerplate required to extract C code and define new streaming types and primitive operations; we plan to generate this automatically in the future.
To define new stream types, one must implement the has_stream typeclass, which provides a type name and a default value.
For fields, one must additionally define primitives for constructors and accessor-functions:

```fstar
-- For a record type, we need to implement has_stream and define the streaming primitives
type ref_message = {
  sof:         ntu;
  master:      master_index;
  cycle_index: cycle_index;
}

instance has_stream_ref_message: Sugar.has_stream ref_message = {
  ty_id       = [`%ref_message];
  val_default = { sof = Sugar.val_default; master = Sugar.val_default; cycle_index = Sugar.val_default; };
}

-- Primitive definition for constructor; splice runs the lift_prim tactic, which generates a lifted primitive of type:
-- > ref_message_new : stream ntu -> stream master_index -> stream cycle_index -> stream ref_message
%splice[ref_message_new] (SugarTac.lift_prim "ref_message_new" (`(fun sof master cycle_index -> {sof; master; cycle_index })))
```

The actual Pipit code is split into [Controller](Network.TTCan.Impl.Controller.fst): top-level driver logic; [Errors](Network.TTCan.Impl.Errors.fst): fault and error checks; [MessageStatus](Network.TTCan.Impl.MessageStatus.fst): message-status-counters, which track errors for a particular message; [States](Network.TTCan.Impl.States.fst): state machines for master-mode and sync-state, as well as computing the current cycle-local-time; [Triggers](Network.TTCan.Impl.Triggers.fst): trigger execution and scheduling; and [Util](Network.TTCan.Impl.Util.fst): utility functions such as rising and falling edges and latches.

## Caveats

There is a known bug in F\* where types with typeclass instances can cause spurious errors. The issue is related to some mismatch between the binary cache and the source file: when the cache is older than the source, implicit typeclass arguments are not inserted properly. If you see the following error, running `make verify` should resolve it:
```
- Expected type "Type"; but "Pipit.Sugar.Shallow.Base.stream (t b)" has type "{| _: Pipit.Sugar.Shallow.Base.has_stream (t b) |} -> Type"
```