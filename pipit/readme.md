# Implementation notes

This document describes the high-level structure of Pipit and what is actually proved.
Pipit is work-in-progress; we're still missing the top-level statement that links together the k-inductive transition-system proofs with the proof obligations.

The module structure is as follows:

## Pipit.Context
Definitions and properties about typing contexts.

## Pipit.Exec
Extraction to C code; tactics for helping extraction. The actual translations are in `Pipit.System.Exec`.

## Pipit.Exp
### Pipit.Exp.Base
Definition of core language.
### Pipit.Exp.Bigstep
Dynamic semantics (Section 3.1), proofs of simple properties such as determinism.
### Pipit.Exp.Binding, Pipit.Exp.Binding.Properties
Substitution and lifting; proof that substitution distributes over substitution.
### Pipit.Exp.Causality
Definition of causality, proofs that evaluation is total, evaluation is substitutive, and that recursive evaluation is productive (Section 3.3, Theorems 1, 2 and 3)
### Pipit.Exp.Checked
Checked semantics (Section 3.2). There is a slight discrepancy between the paper and implementation of checked semantics for contracts. Contracts should descend into the rely and guarantee, but the implementation does not. The paper is correct.
We also use an `admit` here to show that if an expression checks, then the blessed expression checks; this proof is pending.
This discrepancy / admission does not affect the claims made in the paper.


## Pipit.Prim
Definitions of primitive tables.
The core language is parametrised by the primitive table, which makes it easier to define new primitives and types.
The Shallow primitive table allows users to define shallowly-embedded primitives from F\* functions.
The Vanilla primitive table is a small deeply-embedded set of primitives.

The primitive table requires that each type has a type identifier; it also requires that two types with equivalent identifiers are themselves equivalent, as this is used in substitution.
The Shallow primitive table uses shallowly-embedded types, which do not have decidable equality.
To work around this, the Shallow table introduces an axiom that two variables with equal identifiers and type identifiers have the same type.
This axiom is potentially unsafe, but it is limited to users of the Shallow primitive table.
The Shallow primitive table also includes an axiom for partially-decidable equality of primitive operations, which is useful for common subexpression elimination.

The Vanilla primitive table requires no axioms.

## Pipit.Sugar
Syntactic sugar: surface syntax.
### Pipit.Sugar.Check
Helper functions for checking properties.
This module includes some admitted proofs that the proof-obligations on the abstract transition systems relate to the checked semantics.
These proofs are pending and do not affect the claims made in the paper.

### Pipit.Sugar.Contract
Helper functions for checking contracts.

### Pipit.Sugar.Shallow
Syntactic sugar and helper functions specific to the Shallow primitive table.
This module includes an axiom `unsafe_proposition_holds`, which is used to state `prop` propositions as checked Pipit properties.
This module does not expose the axiom and limits users to a restricted, safe interface.
In the future, we wish to embed propositions without requiring such an axiom.

This axiom is limited to users of the Shallow primitive table; it does not affect the soundness of translation for programs using the Vanilla primitive table.

## Pipit.System
Transition systems.

### Pipit.System.Exec, Pipit.System.Exec.Exp
Executable transition systems.
### Pipit.System.Exec.Exp.Properties
Proof of translation equivalence (Section 5, Theorem 5)

### Pipit.System.Exp
Translation of abstract systems (Section 4)
### Pipit.System.Exp.Properties
Proof of translation abstraction (Section 4, Theorem 4)
