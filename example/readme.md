# Pipit examples

We have one medium-sized example and a few small ones.

## Time-triggered Controller Area Network (medium)

TTCAN is a time-triggered network architecture. It is used in the automotive industry.
The time-triggered network has a static schedule which all nodes must statically agree on.
We implement the high-level driver logic, for which we can generate C.
We prove some properties about an abstraction.
[The readme has more information.](ttcan/readme.md)


## Pump (small):
The "pump" example is a controller for a water reservoir.
The implementation of the controller is in the [Pump.Check module](Pump.Check.fst), which also proves some small properties.
The [Pump.Extract module](Pump.Extract.fst) extracts it to C code.

There is a video of the controller in action on [youtube (REDACTED)](REDACTED).

## Fir (tiny):
Finite impulse response filter: see the [Fir.Check module](Fir.Check.fst).
This checks a bounded-input-bounded-output property of a few tiny FIR filters.
The [Fir.CheckN module](Fir.CheckN.fst) shows mixing list induction with Pipit proofs.
