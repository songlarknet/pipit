# Implementation notes

This document describes the high-level structure of Pipit and what is actually proved.
Pipit is work-in-progress; we're still missing the top-level statement that links together the k-inductive transition-system proofs with the proof of correctness of translation.
I have also had some trouble making the proofs of the metatheory work reliably in F\*, and some of the proofs are a bit flaky.

## Core language

The Pipit core language is defined in the [Pipit.Exp.Base module](Pipit.Exp.Base.fst).
Core language has the following grammar.
A hypothetical surface language is shown in the left column while the second column shows the constructor form used in the implementation:

```
e := v                  (XVal v)        values
   | x                  (XVar x)        free variables
   | i                  (XBVar i)       bound de-Bruijn indices
   | f e                (XApp f e)      application
   | v fby e            (XFby v e)      delay (followed-by or pre)
   | rec x. e[x]        (XMu e)         recursive stream
   | let x: τ = e in e'[x]
                        (XLet τ e e')   let-bindings
)
```

The implementation has expressions indexed by the variable-binding context and result type: an expression of type `exp 'c 'a` can refer to variables in the list `'c` and has result type `'a`.
Variable binding contexts are defined in the [Pipit.Context module](Pipit.Context.fst).

Free variables are used only by the surface syntax ([Pipit.Sugar](Pipit.Sugar.fst)) while constructing expressions; they are converted to de Bruijn indices.
The Context module also includes an axiom that states that the surface syntax ensures that free variables are unique:

``` f*
  assume val axiom_variables_require_fresh_indices (x: var 'a) (x': var 'b { Var?.v x = Var?.v x' }): Lemma ('a == 'b)
```

This axiom is used when closing free variables as de Bruijn indices, as we need to know that two occurrences of the same free variable have the same type.
Some form of decidable equality on types may remove the need for this axiom.

Standard operations for manipulating binding-forms are defined in module [Pipit.Exp.Binding](Pipit.Exp.Binding.fst), including substitution and lifting de Bruijn indices.
Module [Pipit.Exp.Binding.Properties](Pipit.Exp.Binding.Properties.fst) includes proofs of standard properties: distributivity of substitution, reordering lifts, and so on.

## Bigstep semantics

We define a bigstep semantics for Pipit with the judgment form `Sigma |- e => v`, where `Sigma` is a sequence of heaps denoting the streaming history.
The rules for the non-streaming primitives are fairly straightforward:

```
Sigma := store | Sigma; store
store := { i = v, ... }


--------------- (BSVal)
Sigma |- v => v


----------------------------- (BSVar)
Sigma |- i => Sigma_0(i)


Sigma |- e => v      Sigma |- e' => v'
-------------------------------------- (BSApp)
      Sigma |- e e' => [| v v' |]
      

Sigma |-      e'[x := e] => v
----------------------------- (BSLet)
Sigma |- let x = e in e' => v
```

Rule (BSVal) says that a value evaluates to itself.
Rule (BSVar) says that a de Bruijn index is evaluated by looking it up in the most recent stream context.
Here we write the most recent stream context in the non-empty history `Sigma` as the zeroth index (`Sigma_0`) but the history is implemented as a reversed list in the implementation.
Rule (BSApp) says that applications evaluate both sides before performing application on the meta-level (written using Oxford brackets `[| v v' |]`).
Rule (BSLet) uses a substitution-based evaluation for let-expressions.

For the streaming primitives:
```
--------------------- (BSFby1)
store |- v fby e => v


Sigma        |-       e => v
----------------------------- (BSFbyS)
Sigma; store |- _ fby e => v


Sigma |- e[x := rec x. e] => v
----------------------------- (BSMu)
Sigma |-        rec x. e  => v
```

Rule (BSFby1) says that delays use the default value when given a streaming history with a single environment (`store`).
Rule (BSFbyS) says that, given a streaming history with more than one value, we evaluate delayed expressions by evaluating the expression in the previous history.
Finally, rule (BSMu) says that we can evaluate recursive streams by unrolling the recursion.
This evaluation rule is not trivially terminating, but we use a causality restriction to ensure termination of well-formed expressions.

We also define a multiple-value bigsteps relation, written as `Sigma |- e =>* vs`, where vs is a non-empty list of values, one for each element of the streaming history.
Finally, we prove that the bigstep relation is deterministic by straightforward induction.
(We can actually prove a slightly stronger property, which is that for a given streaming history and expression, there is a unique bigstep derivation tree.)

## Causality

We define a *causality* restriction to ensure that recursive streams only depend on their previous values (module [Pipit.Exp.Causality](Pipit.Exp.Causality.fst)).
For example, the expression `rec x. x + 1` is not causal, as computing the next value of `x` depends on the value of `x` itself.
If we tried to construct a bigstep derivation tree for this expression, we would just keep applying (BSMu) to unfold the recursion.
Instead, we rule this out with a syntactic restriction that all occurrences of recursive binders must be *guarded* by a delay.
For example, we can fix the above by introducing an initialised delay `rec x. 0 fby (x + 1)`.

We use this causality restriction to prove a variant of progress: *causal expressions always make progress*:

```
non-empty Sigma         causal e
------------------------------- (lemma_bigstep_total)
exists v. Sigma |- e => v
```

This definition states that, for a non-empty streaming history `rows` and a causal expression `e`, there exists some value `v` that it will bigstep to.
We could imagine using this definition as an evaluator, but it has the wrong asymptotic complexity for serious use.

The proof is by induction over the expression `e`, but we run into some trouble with the bigstep relation: the let and rec rules require substitution, but we can't apply the inductive hypothesis to the substituted expression, as it's not necessarily smaller than `e`.

To ensure the induction is well-founded, we prove that the substitution-based rules in the bigstep semantics are equivalent to store-based rules.
For let-expressions, if we want to evaluate `let x = e in e'`, then we can evaluate `e` to the stream of values `vs`, and evaluate `e'` under a context extended with `x` set to `vs`:

```
Sigma |- e =>* vs        x=vs #^ Sigma |- e' => v
----------------------------------------------- (lemma_bigstep_substitute_intros XLet)
Sigma |- let x = e in e' => v
```
The syntax `x=vs #^ Sigma` adds bindings `x = v` from values `vs` to each element of stream history `Sigma`.

We can do a similar substitution for recursive streams `rec x. e[x]`: instead of evaluating `Sigma |- e[x := rec x. e[x]] => v`, we can extend the streaming history with the values of `rec x. e[x]`.
We might imagine that we could evaluate the recursive stream in a heap extended with all of the values of the recursive stream, something like:
```
x=vs #^ Sigma |- e        =>* vs
-------------------------------- (lemma_bigstep_substitute_intros XMu hypothetical)
        Sigma |- rec x. e =>* vs
```
However, we don't yet know what all of the values `vs` are, until we have evaluated `e`.
This cyclic dependency is solved by the causality restriction.
The causality restriction tells us that recursive streams can only depend on previous values of the stream itself: that is, we can put any value at all in the current heap binding, as the recursive expression won't use it. 

The statement says that if we know that the recursive stream previously evaluated to many values `vs`, then to get the next recursive stream value, we can extend the streaming history with a new heap `store` and a dummy value `v_bot` and evaluate the expression to some value `v'`.

```
Sigma |- rec x. e =>* vs      x=(vs; v_bot) #^ (Sigma; store) |- e => v'
--------------------------------------------------------------------- (lemma_bigstep_substitute_intros_no_dep XMu)
             Sigma; store |- rec x. e => v'
```

To synthesise a dummy value, we require recursive streams to be inhabited and define an [`inhabited` typeclass](Pipit.Inhabited.fst).
Will this technique scale to more interesting types that aren't necessarily inhabited?
We might have to modify the stores to contain an explicit bottom value.

## Transition systems

We define a translation to transition systems so that we can prove properties on the translated system.
We define two kinds of transition systems: functional and relational (``non-deterministic'').
The entire language of causal expressions as it currently exists can be translated to functional transition systems.
To represent assume/guarantee-style contracts in the future we will need to use relational transition systems.

Functional systems and combinators are defined in the [Pipit.System.Det module](Pipit.System.Det.fst) with the following type:

``` f*
noeq
type dsystem (input: Type) (state: Type) (result: Type) = {
  init: state;

  step:
    (* Values of input variables *)
    i: input ->
    (* Starting state *)
    s: state ->
    (* Updated state and result *)
    (state & result);

  (* Properties to check *)
  chck: checks state;
}
```

The translation from causal expressions to transition system has the following type:

``` f*
val dsystem_of_exp (e: exp 'c 'a { Causal.causal e }):
    dsystem (C.row 'c) (state_of_exp e) 'a
```

The translation takes an expression with de Bruijn variable context `'c` and result type `'a` and returns a functional system that accepts rows of context `'c` (a statically-indexed heap), with an internal state depending on the structure of the expression, and a result type of `'a`.
The internal state is fairly simple, and really just gives each delay expression an internal buffer in which to store the delayed value:

``` f*
let rec state_of_exp (e: exp 'c 'a): Tot Type (decreases e) =
  match e with
  | XVal v              -> unit
  | XBVar x             -> unit
  | XVar x              -> unit
  | XApp f e            -> state_of_exp f & state_of_exp e
  | XFby v e1           -> state_of_exp e1 & 'a
  | XMu _ e1            -> state_of_exp e1
  | XLet b e1 e2        -> state_of_exp e1 & state_of_exp e2
```

To prove that the translation is correct, we define an invariant that connects the transition system's internal state to the bigstep semantics.
The key part of the invariant is that each delayed buffer in the internal state corresponds to the evaluation in the bigstep semantics.

The statement of the translation correctness says that, for a streaming history and list of result values that are related by the bigstep-many relation, then feeding the history into the translated system results in the same values.

```
           Sigma |- e =>* vs
----------------------------------------- (dstep_eval_complete)
xsystem_stepn (dsystem_of_exp e) Sigma vs
```

In the future, we expect to use a combination of functional and relational transition systems.
The functional systems provide a cleaner representation for directly-executable code, while the relational systems are necessary to describe abstract behaviours.
