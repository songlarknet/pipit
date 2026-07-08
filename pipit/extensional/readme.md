# Pipit.Extensional

`Pipit.Extensional` is the home for extensional (observational) semantics.

The intent is to provide:

- function-of-stream-step representations (`nat -> a`) for streams/traces,
- observational equivalence principles for systems,
- rewrite laws (equational reasoning) that preserve observable behavior,
- bridges from system proofs (e.g. induction) to stream-level properties.

This package depends on `base` and `abstract`.

## Design

The goal is a program logic `{ P } s { Q }` over streams, where

- `P: stream input -> stream prop` is a stream of preconditions,
- `s` is a stream transformer realised by a transition `system`, and
- `Q: stream input -> stream output -> stream prop` is a stream of
	postconditions.

Key decisions (see notes below):

- **Total-function streams** (`nat -> a`). The real transition system
	(`Pipit.System.Base.system`) is deterministic and causal by construction, so
	its observable output is already a total function `nat -> a`. Nondeterminism
	is modelled by oracles, not by a relational stream, so nothing is lost by
	going total — and equational rewriting becomes plain `stream_eq`.
- **`sofar`-based triples over `stream prop`.** The judgement is
	`forall n. sofar (P is) n ==> sofar (Q is (s is)) n`. Using `stream prop`
	(not a single whole-stream `prop`) is what makes the guarded recursion rule
	statable, since it can talk about `pre (Q x)`.
- **Recursion as a system combinator.** `Pipit.System.Base.system_mu` encodes
	the recursive knot with an oracle supplying the recursive value and an
	assumption tying it to the body's output. The guarded rule is

	```
	{ fun ixs n -> P (source ixs) n /\ pre (Q (source ixs) (feedback ixs)) n }
	  body
	{ fun ixs os n -> Q (source ixs) os n }
	--------
	{ P } system_mu body { Q }
	```

	where `source ixs = map snd ixs` and `feedback ixs = map fst ixs`.

Three proof techniques are supported: Hoare-style rules, equational rewriting
(`stream_eq` / `observational_equiv`), and induction over transition systems.

## Current modules

- `Pipit.Extensional.Base`: core stream/pstream/pobs types only.
- `Pipit.Extensional.Stream`: stream combinators and predicates — `const`,
	`eq`, `holds`, the `holds_of_eq` transport lemma, and `sofar`.
- `Pipit.Extensional.PStream`: proof-carrying stream equality (`eq`),
	projections, and equality-transport lemmas.
- `Pipit.Extensional.System`: stream projections of system behavior and
	observational-equivalence predicates.
- `Pipit.Extensional.Logic`: the `sofar`-based triple over a state/oracle-hiding
	`sys` package. Preconditions/postconditions are `stream prop` transformers;
	the judgement quantifies the oracle stream (restricted to runs where the
	rely-assumptions hold so far) and bundles the postcondition with the
	system's obligations in the consequent.

The `system_mu` rule and the equational-rewriting / induction rules are being
rebuilt on top of these foundations.
