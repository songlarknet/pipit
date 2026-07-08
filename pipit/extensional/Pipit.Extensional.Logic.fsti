(* Extensional program logic over transition systems: the user-facing
   judgement, causality side-conditions, and the guarded recursion rule [mu].

   The judgement [triple P t Q] reads: for every input stream [is] and every
   oracle stream that keeps the system's rely-assumptions satisfied so far, if
   the precondition stream [P is] holds so far, then both the postcondition
   stream [Q is os] and the system's own obligations hold so far — where [os]
   is the observable output stream produced by [t].

   Preconditions and postconditions are [stream prop] transformers, and the
   judgement is closed under prefixes via [sofar], which is what makes the
   guarded recursion rule statable. Proofs live in the companion [.fst].
*)
module Pipit.Extensional.Logic

module E  = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module S  = Pipit.Extensional.System
module SB = Pipit.System.Base

(* Extensional triple judgement.

   Universally quantifies the oracle stream, restricting to runs where the
   rely-assumptions have held so far. The consequent bundles the caller's
   postcondition [Q] with the system's own obligations. *)
let triple
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (t: S.sys input output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : prop
  =
  forall (is: E.stream input)
         (orc: E.stream (SB.option_type_sem t.oracle))
         (n: nat).
    let ios = S.with_oracle t is orc in
    let os  = S.stream_of_output t.raw ios in
    ES.sofar (p is) n ==>
    ES.sofar (S.stream_of_assumptions t.raw ios) n ==>
    (ES.sofar (q is os) n /\
     ES.sofar (S.stream_of_obligations t.raw ios) n)

(*** Guarded recursion ***)

(* Projections of a [mu]-body input stream: the source input and the recursive
   feedback (the candidate output being defined). *)
let source
  (#input #output: Type)
  (ixs: E.stream (output & input))
  : E.stream input
  =
  fun n -> snd (ixs n)

let feedback
  (#input #output: Type)
  (ixs: E.stream (output & input))
  : E.stream output
  =
  fun n -> fst (ixs n)

(* A stream predicate is causal (prefix-determined / a safety property) when its
   truth at step [n] depends only on the stream prefix up to [n]. *)
let causal
  (#a: Type)
  (p: E.stream a -> E.stream prop)
  : prop
  =
  forall (xs1 xs2: E.stream a) (n: nat).
    (forall (k: nat). k <= n ==> xs1 k == xs2 k) ==>
    (p xs1 n <==> p xs2 n)

(* The postcondition analogue of [causal] over an input and an output stream.
   NB: this is deliberately the explicit two-stream form rather than
   [causal (fun ios -> q (map fst ios) (map snd ios))]. The combined form is
   strictly weaker to use: recovering [q is1 os1 n <==> q is2 os2 n] from it
   would require rewriting [map fst (join is1 os1)] back to [is1], i.e.
   plain-arrow eta/functional extensionality, which F* does not provide. *)
let causal_post
  (#input #output: Type)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : prop
  =
  forall (is1 is2: E.stream input) (os1 os2: E.stream output) (n: nat).
    (forall (k: nat). k <= n ==> is1 k == is2 k) ==>
    (forall (k: nat). k <= n ==> os1 k == os2 k) ==>
    (q is1 os1 n <==> q is2 os2 n)

(* Guarded body precondition: [P] on the source input, and [pre (Q x)] on the
   recursive feedback [x]. *)
let mu_body_pre
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (ixs: E.stream (output & input))
  : E.stream prop
  =
  fun n -> p (source ixs) n /\ ES.pre (q (source ixs) (feedback ixs)) n

(* Body postcondition: [Q] on the source input and the body output. *)
let mu_body_post
  (#input #output: Type)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (ixs: E.stream (output & input))
  (os: E.stream output)
  : E.stream prop
  =
  fun n -> q (source ixs) os n

(* Guarded recursion rule for [System.mu]:

     Q causal
     { fun ixs n -> P (source ixs) n /\ pre (Q (source ixs) (feedback ixs)) n }
       body
     { fun ixs os n -> Q (source ixs) os n }
     -------------------------------------------------------------------------
     { P } System.mu body { Q }
*)
val mu
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (body: S.sys (output & input) output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      causal p /\
      causal_post q /\
      triple (mu_body_pre p q) body (mu_body_post q))
    (ensures
      triple p (S.mu body) q)
