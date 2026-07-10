(* Observational-equivalence predicates for transition systems.

   Systems are compared extensionally by their output/check streams, not by
   internal state representation. These predicates underpin the
   equational-rewriting proof technique.
*)
module Pipit.Extensional.System.Eq

module E = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module EPS = Pipit.Extensional.PStream
module S = Pipit.Extensional.System
module SB = Pipit.System.Base

(* Extensional equivalence on outputs only. *)
let output_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: SB.system input oracle state result)
  : prop
  =
  forall (ios: S.io_stream input oracle).
    ES.eq
      (S.stream_of_output t1 ios)
      (S.stream_of_output t2 ios)

(* Full observational equivalence: outputs and check streams agree. *)
let observational_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: SB.system input oracle state result)
  : prop
  =
  forall (ios: S.io_stream input oracle).
    EPS.eq
      (S.pstream_of_system t1 ios)
      (S.pstream_of_system t2 ios)

(* Observational equivalence is reflexive. *)
let observational_equiv_refl
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state result)
  : Lemma (ensures observational_equiv t t)
  =
  ()

(* Full observational equivalence implies output equivalence. *)
let output_equiv_of_observational_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: SB.system input oracle state result)
  : Lemma
    (requires observational_equiv t1 t2)
    (ensures output_equiv t1 t2)
  =
  introduce forall (ios: S.io_stream input oracle).
    ES.eq (S.stream_of_output t1 ios) (S.stream_of_output t2 ios)
  with (
    EPS.values_eq_of_eq
      (S.pstream_of_system t1 ios)
      (S.pstream_of_system t2 ios)
  )

(* Output-equivalent systems preserve any pointwise output-stream predicate
   under the same input stream. *)
let stream_holds_of_output_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: SB.system input oracle state result)
  (ios: S.io_stream input oracle)
  (p: result -> prop)
  : Lemma
    (requires
      output_equiv t1 t2 /\
      ES.holds p (S.stream_of_output t1 ios))
    (ensures
      ES.holds p (S.stream_of_output t2 ios))
  =
  ES.holds_of_eq p
    (S.stream_of_output t1 ios)
    (S.stream_of_output t2 ios)

(* Observationally equivalent systems preserve pointwise predicates over
   the assumptions stream. *)
let stream_holds_of_assumptions_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: SB.system input oracle state result)
  (ios: S.io_stream input oracle)
  (p: prop -> prop)
  : Lemma
    (requires
      observational_equiv t1 t2 /\
      ES.holds p (S.stream_of_assumptions t1 ios))
    (ensures
      ES.holds p (S.stream_of_assumptions t2 ios))
  =
  EPS.assumptions_eq_of_eq
    (S.pstream_of_system t1 ios)
    (S.pstream_of_system t2 ios);
  ES.holds_of_eq p
    (S.stream_of_assumptions t1 ios)
    (S.stream_of_assumptions t2 ios)

(* Observationally equivalent systems preserve pointwise predicates over
   the obligations stream. *)
let stream_holds_of_obligations_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: SB.system input oracle state result)
  (ios: S.io_stream input oracle)
  (p: prop -> prop)
  : Lemma
    (requires
      observational_equiv t1 t2 /\
      ES.holds p (S.stream_of_obligations t1 ios))
    (ensures
      ES.holds p (S.stream_of_obligations t2 ios))
  =
  EPS.obligations_eq_of_eq
    (S.pstream_of_system t1 ios)
    (S.pstream_of_system t2 ios);
  ES.holds_of_eq p
    (S.stream_of_obligations t1 ios)
    (S.stream_of_obligations t2 ios)

(*** Package-level observational equivalence (state-blind) ***)

(* Observational equivalence at the [sys] package level. The two systems must
   share the same oracle type but may have *different* state representations —
   only their observable streams are compared, run under the same input and
   oracle stream. This is what CSE-style rewrites need, since sharing a
   subcomputation changes the state shape; and unlike [observational_equiv] it
   does not fix the state type. It carries no [oracle == None] restriction, so
   the transport and congruence rules built on it apply to oracle-carrying
   systems too — the oracle-free case (e.g. CSE) is just the [oracle == None]
   instance, where the oracle stream is the unique unit stream. *)
let equiv
  (#input #output: Type)
  (t1: S.sys input output)
  (t2: S.sys input output { t2.oracle == t1.oracle })
  : prop
  =
  forall (is: E.stream input)
         (orc: E.stream (SB.option_type_sem t1.oracle))
         (n: nat).
    let ios1 = S.with_oracle t1 is orc in
    let ios2 = S.with_oracle t2 is orc in
    S.stream_of_output t1.raw ios1 n == S.stream_of_output t2.raw ios2 n /\
    (S.stream_of_assumptions t1.raw ios1 n <==> S.stream_of_assumptions t2.raw ios2 n) /\
    (S.stream_of_obligations t1.raw ios1 n <==> S.stream_of_obligations t2.raw ios2 n)

let equiv_refl
  (#input #output: Type)
  (t: S.sys input output)
  : Lemma (equiv t t)
  = ()

let equiv_sym
  (#input #output: Type)
  (t1: S.sys input output)
  (t2: S.sys input output { t2.oracle == t1.oracle })
  : Lemma (requires equiv t1 t2) (ensures equiv t2 t1)
  = ()

(* Applicative common-subexpression law: applying a binary function to two runs
   of the *same* deterministic system [t] is the same as running [t] once and
   applying the diagonal. This is the core CSE rewrite —
   [ap (map f t) t] has two copies of [t]'s state, [map (fun x -> f x x) t] has
   one, and [equiv] equates them across that state change. Both sides are
   oracle-free, so this is the [oracle == None] instance of [equiv]. *)
#push-options "--split_queries always --z3rlimit 60"
let lemma_ap_map_cse
  (#input #a #b: Type)
  (f: a -> a -> b)
  (t: S.sys input a { t.oracle == None })
  : Lemma (equiv (S.ap (S.map f t) t) (S.map (fun (x: a) -> f x x) t))
  =
  let lhs = S.ap (S.map f t) t in
  let rhs = S.map (fun (x: a) -> f x x) t in
  introduce forall (is: E.stream input)
                   (orc: E.stream (SB.option_type_sem lhs.oracle))
                   (n: nat).
      (let ios1 = S.with_oracle lhs is orc in
       let ios2 = S.with_oracle rhs is orc in
       S.stream_of_output lhs.raw ios1 n == S.stream_of_output rhs.raw ios2 n /\
       (S.stream_of_assumptions lhs.raw ios1 n <==> S.stream_of_assumptions rhs.raw ios2 n) /\
       (S.stream_of_obligations lhs.raw ios1 n <==> S.stream_of_obligations rhs.raw ios2 n))
  with begin
    let ios1 = S.with_oracle lhs is orc in
    let ios2 = S.with_oracle rhs is orc in
    let iof = S.io_fst #input #(S.map f t).oracle #t.oracle ios1 in
    let ios = S.io_snd #input #(S.map f t).oracle #t.oracle ios1 in
    (* For [None] oracles the projections are the identity, and both packages
       feed the same (unit) oracle, so all three io-streams coincide. *)
    assert (forall (k: nat). iof k == ios1 k);
    assert (forall (k: nat). ios k == ios1 k);
    assert (forall (k: nat). ios1 k == ios2 k);
    (* Outer [ap]: split output/checks into the two operands. *)
    S.lemma_ap (S.map f t) t ios1 n;
    (* Inner [map f t] on the left projection. *)
    S.lemma_map f t iof n;
    (* Right operand [t] on the right projection. *)
    S.lemma_map (fun (x: a) -> f x x) t ios2 n;
    (* Congruences: rewrite every [t]-observation to the common [ios1]. *)
    S.lemma_stream_of_output_congruence t.raw iof ios1 n;
    S.lemma_stream_of_output_congruence t.raw ios ios1 n;
    S.lemma_stream_of_output_congruence t.raw ios1 ios2 n;
    S.lemma_stream_of_assumptions_congruence t.raw iof ios1 n;
    S.lemma_stream_of_assumptions_congruence t.raw ios ios1 n;
    S.lemma_stream_of_assumptions_congruence t.raw ios1 ios2 n;
    S.lemma_stream_of_obligations_congruence t.raw iof ios1 n;
    S.lemma_stream_of_obligations_congruence t.raw ios ios1 n;
    S.lemma_stream_of_obligations_congruence t.raw ios1 ios2 n;
    assert (S.stream_of_output lhs.raw ios1 n ==
            f (S.stream_of_output t.raw ios1 n) (S.stream_of_output t.raw ios1 n));
    assert (S.stream_of_output rhs.raw ios2 n ==
            f (S.stream_of_output t.raw ios1 n) (S.stream_of_output t.raw ios1 n))
  end
#pop-options

(* Eliminator: extract [equiv]'s per-index agreement at a chosen input, oracle
   and step. Lives in this module so [equiv] unfolds locally. *)
let equiv_elim
  (#input #output: Type)
  (t1: S.sys input output)
  (t2: S.sys input output { t2.oracle == t1.oracle })
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem t1.oracle))
  (n: nat)
  : Lemma
    (requires equiv t1 t2)
    (ensures (
      let ios1 = S.with_oracle t1 is orc in
      let ios2 = S.with_oracle t2 is orc in
      S.stream_of_output t1.raw ios1 n == S.stream_of_output t2.raw ios2 n /\
      (S.stream_of_assumptions t1.raw ios1 n <==> S.stream_of_assumptions t2.raw ios2 n) /\
      (S.stream_of_obligations t1.raw ios1 n <==> S.stream_of_obligations t2.raw ios2 n)))
  = ()




