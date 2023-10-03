# Version 0:
Goals for V0:
* compositional proofs, contracts, and partially-verified codegen

Non-goals for V0:
* verification of bounded integers in codegen

## Contracts and compositionality ✅
* Compositional proofs to avoid re-checking
* Contracts for abstracting details

## Case studies
### Coffee machine ("pump") ✅
* Tiny
* Useful as running example
* Nice video

### Kind2 / CoCoSpec contracts example
* Port case study from Kind2 paper
* Uses clock-free subset of Lustre
* Not that interesting metaprogramming
* < 3kloc including spec

https://github.com/kind2-mc/cocospec_tcm_experiments/blob/master/systems/cocospec_comp_system.lus

### Statically-scheduled network (CAN bus)
* CAN bus example with static schedule
* Availability and latency guarantees
* Interesting metaprogramming

## Meta-theory proofs
Old proofs need to be updated:
* causality
* substitution
* transition system refines program
* k-induction correctness

New proofs:
* composition of checked programs
* program refines transition system
* transition checks imply program checks

## Optional / as necessary

### Common subexpression elimination
* May be needed to verify larger programs
* Allows statement of invariants
* Can re-use F* let syntax

### Optimised translation for pure functions
* Systems get very complex states with lots of nested tuples of units
* Pure systems do not need state at all: simplify away
