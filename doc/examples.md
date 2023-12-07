# Ideas for examples

## Kind2 benchmarks


### Tramway
* https://github.com/kind2-mc/kind2-benchmarks/blob/master/FMCAD08/Bool/simulation/tramway.lus

Small, but well-documented.

### Triplex voter
* https://github.com/kind2-mc/kind2-benchmarks/blob/master/FunctionalChain/functionalChain_str_small.lus

Small, well-documented.

### Cache coherency protocols:
* https://github.com/kind2-mc/kind2-benchmarks/blob/master/FMCAD08/Int/memory1/DRAGON_1.lus
* https://en.wikipedia.org/wiki/Cache_coherency_protocols_(examples)

There are many variations on this in the Kind2 benchmarks repository. They all seem quite similar. Would it be possible to somehow encode these variations in one parameterised model?

Not much explanation.

### Cruise controller
* https://github.com/kind2-mc/kind2/blob/develop/examples/cruise_controller.lus

Generated from Simulink or something. Difficult to read.

### Microwave
* https://github.com/kind2-mc/kind2/blob/develop/examples/microwave.lus

Generated, difficult to read.

### Cocospec examples
* https://github.com/kind2-mc/cocospec_tcm_experiments/blob/master/systems/cocospec_comp_system.lus

Generated, but maybe not too bad.

## Djed
Djed: A Formally Verified Crypto-Backed Pegged Algorithmic Stablecoin
* https://eprint.iacr.org/2021/1069.pdf

Model implemented and checked in Kind2. Some aspects couldn't be proved or modeled in Kind2, so it also has Isabelle proofs.
If we could model both aspects (Kind2 model + Isabelle proofs), it would be neat.
