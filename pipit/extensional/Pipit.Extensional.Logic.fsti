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

(*** Structural rules ***)

(* Rule of consequence: strengthen the precondition and weaken the postcondition.
   Purely structural — [os] is the fixed actual output, so no causality is needed.

     { P' } t { Q' }
     forall is n.    sofar (P is) n ==> sofar (P' is) n
     forall is os n. sofar (P is) n ==> sofar (Q' is os) n ==> sofar (Q is os) n
     ----------------------------------------------------------------------------
     { P } t { Q }
*)
val consequence
  (#input #output: Type)
  (t: S.sys input output)
  (p p': E.stream input -> E.stream prop)
  (q q': E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      triple p' t q' /\
      (forall (is: E.stream input) (n: nat).
         ES.sofar (p is) n ==> ES.sofar (p' is) n) /\
      (forall (is: E.stream input) (os: E.stream output) (n: nat).
         ES.sofar (p is) n ==> ES.sofar (q' is os) n ==> ES.sofar (q is os) n))
    (ensures triple p t q)

(*** Transition-system induction ***)

(* Per-step verification condition for [induct1]. For every input/oracle stream
   and step [n], assuming the precondition [P] and the system's assumptions hold
   so far, and the postcondition [Q] and obligations held at every *strictly
   earlier* step, re-establish [Q] and the obligation at step [n].

   This folds the stream pre/postcondition into a 1-induction over the transition
   system: [P] (so far) is an extra hypothesis, [Q n] and the obligation at [n]
   are the goals, and the induction hypothesis supplies [Q]/obligations before
   [n]. After unfolding to a concrete system, [stream_of_output t.raw ios n]
   exposes [t.step (ios n) (prev state)], so the step reasoning is discharged
   against the system's own transition function. *)
let induct1_vc
  (#input #output: Type)
  (t: S.sys input output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : prop
  =
  forall (is: E.stream input)
         (orc: E.stream (SB.option_type_sem t.oracle))
         (n: nat).
    let ios = S.with_oracle t is orc in
    let os  = S.stream_of_output t.raw ios in
    (ES.sofar (p is) n /\
     ES.sofar (S.stream_of_assumptions t.raw ios) n /\
     (forall (k: nat). k < n ==> q is os k) /\
     (forall (k: nat). k < n ==> S.stream_of_obligations t.raw ios k))
    ==>
    (q is os n /\ S.stream_of_obligations t.raw ios n)

(* Transition-system 1-induction: discharge a triple by its per-step VC. *)
val induct1
  (#input #output: Type)
  (t: S.sys input output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires induct1_vc t p q)
    (ensures triple p t q)

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
      ES.causal p /\
      ES.causal2 q /\
      triple (mu_body_pre p q) body (mu_body_post q))
    (ensures
      triple p (S.mu body) q)

(* Leaf rule for [System.id]. It outputs its input verbatim and has no checks, so
   the triple is a pure stream-logic implication with the output taken to be the
   input:

     Q causal
     forall is n. sofar (P is) n ==> sofar (Q is is) n
     -------------------------------------------------
     { P } System.id { Q }
*)
val id
  (#a: Type)
  (p: E.stream a -> E.stream prop)
  (q: E.stream a -> E.stream a -> E.stream prop)
  : Lemma
    (requires
      ES.causal2 q /\
      (forall (is: E.stream a) (n: nat). ES.sofar (p is) n ==> ES.sofar (q is is) n))
    (ensures
      triple p (S.id #a) q)

(* Rule for [System.fby]. Since [fby v0 t] only shifts the output (its checks are
   [t]'s at the current step), a triple for [t] whose postcondition is [q]
   post-composed with the shift [ES.fby v0] transfers to [fby v0 t]:

     Q causal
     { P } t { fun is ot -> Q is (v0 fby ot) }
     -----------------------------------------
     { P } System.fby v0 t { Q }
*)
val fby
  (#input #output: Type)
  (v0: output)
  (t: S.sys input output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      ES.causal2 q /\
      triple p t (fun is ot -> q is (ES.fby v0 ot)))
    (ensures
      triple p (S.fby v0 t) q)

(* Rule for [System.map]. Like [fby], [map f t] only transforms the output
   (checks unchanged), so a triple for [t] with [q] post-composed with the map
   [ES.map f] transfers to [map f t]:

     Q causal
     { P } t { fun is ot -> Q is (map f ot) }
     -----------------------------------------
     { P } System.map f t { Q }
*)
val map
  (#input #output1 #output2: Type)
  (f: output1 -> output2)
  (t: S.sys input output1)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output2 -> E.stream prop)
  : Lemma
    (requires
      ES.causal2 q /\
      triple p t (fun is ot -> q is (ES.map f ot)))
    (ensures
      triple p (S.map f t) q)

(*** Oracle-free guarded recursion ***)

(* Oracle-free guarded recursion rule for [System.mufby]. [mufby v0 body]
   introduces no oracle: its feedback is the previous output, delayed by
   [v0 fby -] and carried in state. Soundness is derived from [mu] applied to
   [System.delayed_body v0 body] (the [mu]-body that delays the guessed
   feedback), so the premise is exactly [mu]'s premise for that delayed body:

     P causal, Q causal
     { fun ixs n -> P (source ixs) n /\ pre (Q (source ixs) (feedback ixs)) n }
       System.delayed_body v0 body
     { fun ixs os n -> Q (source ixs) os n }
     -------------------------------------------------------------------------
     { P } System.mufby v0 body { Q }
*)
val mufby
  (#input #output: Type)
  (v0: output)
  (body: S.sys (output & input) output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      ES.causal p /\
      ES.causal2 q /\
      triple (mu_body_pre p q) (S.delayed_body v0 body) (mu_body_post q))
    (ensures
      triple p (S.mufby v0 body) q)

(* Body precondition for the convenience rule [mufby_step]: [P] on the source,
   the feedback seeded at [v0], and [pre (Q -)] applied to the *un-delayed*
   feedback [later feedback]. The [later] cancels [delayed_body]'s [fby], so this
   specialises to [mu_body_pre] on the delayed body. It stays causal because the
   [later] only ever occurs under a matching [pre]. *)
let mufby_guard
  (#input #output: Type)
  (v0: output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (jxs: E.stream (output & input))
  : E.stream prop
  =
  fun n ->
    p (source jxs) n /\
    feedback jxs 0 == v0 /\
    ES.pre (q (source jxs) (ES.later (feedback jxs))) n

(* [mufby_guard] is causal, so it composes with rules (e.g. [mu]) that require a
   causal precondition: the non-causal [later] is always guarded by [pre]. *)
val lemma_mufby_guard_causal
  (#input #output: Type)
  (v0: output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires ES.causal p /\ ES.causal2 q)
    (ensures ES.causal (mufby_guard v0 p q))

(* Convenience oracle-free recursion rule: discharge [mufby]'s premise from a
   triple about [body] itself (fed the delayed feedback), rather than about
   [delayed_body v0 body]:

     P causal, Q causal
     { mufby_guard v0 P Q } body { fun ixs os -> Q (source ixs) os }
     -------------------------------------------------------------------
     { P } System.mufby v0 body { Q }
*)
val mufby_step
  (#input #output: Type)
  (v0: output)
  (body: S.sys (output & input) output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      ES.causal p /\
      ES.causal2 q /\
      triple (mufby_guard v0 p q) body (mu_body_post q))
    (ensures
      triple p (S.mufby v0 body) q)
