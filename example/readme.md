# Pipit examples

We have a few small examples:

## Pump:
The "pump" example is a controller for a water reservoir.
The implementation of the controller is in the [Pump.Check module](Pump.Check.fst), which also proves some small properties.
The [Pump.Extract module](Pump.Extract.fst) extracts it to C code.

There is a video of the controller in action on [youtube](https://youtu.be/6IybbQFPOl8).

## Fir:
Finite impulse response filter: see the [Fir.Check module](Fir.Check.fst).
This checks a bounded-input-bounded-output property of a few tiny FIR filters.
