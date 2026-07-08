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
