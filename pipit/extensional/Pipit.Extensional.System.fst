(* Extensional stream semantics for transition systems.

   This module provides stream projections of a system's observable
   behavior and predicates for observational equivalence.

   The key design choice is to compare systems extensionally by their
   output/check streams, not by internal state representation.
*)
module Pipit.Extensional.System

module E = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module EPS = Pipit.Extensional.PStream

open Pipit.System.Base

(* Input stream consumed by a system step-by-step. *)
type io_stream (input: Type) (oracle: option Type) =
  E.stream (input & option_type_sem oracle)

(* Execute exactly n+1 steps and return the final step result.
   n = 0 corresponds to one step from init using ios 0. *)
let rec step_result_at
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (ios: io_stream input oracle)
  (n: nat)
  : Tot (step_result state result)
  (decreases n)
  =
  match n with
  | 0 ->
    let (i, o) = ios 0 in
    t.step i o t.init
  | _ ->
    let pre = step_result_at t ios (n - 1) in
    let (i, o) = ios n in
    t.step i o pre.s

(* Full proof-carrying observation stream of a system. *)
let pstream_of_system
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (ios: io_stream input oracle)
  : E.pstream result
  =
  fun n ->
    let stp = step_result_at t ios n in
    {
      pv = stp.v;
      pasm = option_prop_sem stp.chck.assumptions;
      pobl = option_prop_sem stp.chck.obligations;
    }

(* Observable output stream. *)
let stream_of_output
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (ios: io_stream input oracle)
  : E.stream result
  =
  EPS.values (pstream_of_system t ios)

(* Observable assumptions stream: did assumptions hold at each step? *)
let stream_of_assumptions
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (ios: io_stream input oracle)
  : E.stream prop
  =
  EPS.assumptions (pstream_of_system t ios)

(* Observable obligations stream: were obligations satisfied at each step? *)
let stream_of_obligations
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (ios: io_stream input oracle)
  : E.stream prop
  =
  EPS.obligations (pstream_of_system t ios)

(* Split the oracle/input stream used by [system_let] into the left
   component consumed by [t1]. *)
let let_ios_left
  (#input: Type)
  (#oracle1 #oracle2: option Type)
  (ios: io_stream input (oracle1 `type_join` oracle2))
  : io_stream input oracle1
  =
  fun n ->
    let io = ios n in
    (fst io, type_join_fst (snd io))

(* Build the right-component input stream consumed by [t2], given an
   extension function and a stream of values from [t1]. *)
let let_ios_right
  (#input #input' #v1: Type)
  (#oracle1 #oracle2: option Type)
  (extend: input -> v1 -> input')
  (ios: io_stream input (oracle1 `type_join` oracle2))
  (x: E.stream v1)
  : io_stream input' oracle2
  =
  fun n ->
    let io = ios n in
    (extend (fst io) (x n), type_join_snd (snd io))

(* Step-indexed alignment for [system_let]: the right state/output match
   running [t2] on the stream extended with [t1]'s outputs. *)
let rec lemma_step_result_at_system_let
  (#input #input' #v1 #v2: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (extend: input -> v1 -> input')
  (t1: system input oracle1 state1 v1)
  (t2: system input' oracle2 state2 v2)
  (ios: io_stream input (oracle1 `type_join` oracle2))
  (n: nat)
  : Lemma
    (ensures
      type_join_fst (step_result_at (system_let extend t1 t2) ios n).s ==
      (step_result_at t1 (let_ios_left ios) n).s /\
      type_join_snd (step_result_at (system_let extend t1 t2) ios n).s ==
      (step_result_at t2
        (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))
        n).s /\
      (step_result_at (system_let extend t1 t2) ios n).v ==
      (step_result_at t2
        (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))
        n).v)
    (decreases n)
  =
  match n with
  | 0 ->
    ()
  | _ ->
    lemma_step_result_at_system_let extend t1 t2 ios (n - 1)

(* Extensional law for [system_let] outputs.
   Intuition: run [def = t1] first, then feed its output stream into [body = t2]
   through [extend]. *)
let stream_of_output_system_let
  (#input #input' #v1 #v2: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (extend: input -> v1 -> input')
  (t1: system input oracle1 state1 v1)
  (t2: system input' oracle2 state2 v2)
  (ios: io_stream input (oracle1 `type_join` oracle2))
  : Lemma
    (ensures
      ES.eq
        (stream_of_output (system_let extend t1 t2) ios)
        (stream_of_output t2
          (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))))
  =
  introduce forall (n: nat).
    stream_of_output (system_let extend t1 t2) ios n ==
    stream_of_output t2
      (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))
      n
  with (
    lemma_step_result_at_system_let extend t1 t2 ios n
  )

(* Extensional equivalence on outputs only. *)
let output_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: system input oracle state result)
  : prop
  =
  forall (ios: io_stream input oracle).
    ES.eq
      (stream_of_output t1 ios)
      (stream_of_output t2 ios)

(* Full observational equivalence: outputs and check streams agree. *)
let observational_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: system input oracle state result)
  : prop
  =
  forall (ios: io_stream input oracle).
    EPS.eq
      (pstream_of_system t1 ios)
      (pstream_of_system t2 ios)

(* Observational equivalence is reflexive. *)
let observational_equiv_refl
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  : Lemma (ensures observational_equiv t t)
  =
  ()

(* Full observational equivalence implies output equivalence. *)
let output_equiv_of_observational_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: system input oracle state result)
  : Lemma
    (requires observational_equiv t1 t2)
    (ensures output_equiv t1 t2)
  =
  introduce forall (ios: io_stream input oracle).
    ES.eq (stream_of_output t1 ios) (stream_of_output t2 ios)
  with (
    EPS.values_eq_of_eq
      (pstream_of_system t1 ios)
      (pstream_of_system t2 ios)
  )

(* Output-equivalent systems preserve any pointwise output-stream predicate
   under the same input stream. *)
let stream_holds_of_output_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: system input oracle state result)
  (ios: io_stream input oracle)
  (p: result -> prop)
  : Lemma
    (requires
      output_equiv t1 t2 /\
      ES.holds p (stream_of_output t1 ios))
    (ensures
      ES.holds p (stream_of_output t2 ios))
  =
  ES.holds_of_eq p
    (stream_of_output t1 ios)
    (stream_of_output t2 ios)

(* Observationally equivalent systems preserve pointwise predicates over
   the assumptions stream. *)
let stream_holds_of_assumptions_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: system input oracle state result)
  (ios: io_stream input oracle)
  (p: prop -> prop)
  : Lemma
    (requires
      observational_equiv t1 t2 /\
      ES.holds p (stream_of_assumptions t1 ios))
    (ensures
      ES.holds p (stream_of_assumptions t2 ios))
  =
  EPS.assumptions_eq_of_eq
    (pstream_of_system t1 ios)
    (pstream_of_system t2 ios);
  ES.holds_of_eq p
    (stream_of_assumptions t1 ios)
    (stream_of_assumptions t2 ios)

(* Observationally equivalent systems preserve pointwise predicates over
   the obligations stream. *)
let stream_holds_of_obligations_equiv
  (#input #result: Type)
  (#oracle #state: option Type)
  (t1 t2: system input oracle state result)
  (ios: io_stream input oracle)
  (p: prop -> prop)
  : Lemma
    (requires
      observational_equiv t1 t2 /\
      ES.holds p (stream_of_obligations t1 ios))
    (ensures
      ES.holds p (stream_of_obligations t2 ios))
  =
  EPS.obligations_eq_of_eq
    (pstream_of_system t1 ios)
    (pstream_of_system t2 ios);
  ES.holds_of_eq p
    (stream_of_obligations t1 ios)
    (stream_of_obligations t2 ios)

(* Step-indexed execution of [system_const] always returns the same value. *)
let rec lemma_step_result_at_system_const
  (#input #result: Type)
  (v: result)
  (ios: io_stream input None)
  (n: nat)
  : Lemma
    (ensures (step_result_at (system_const v) ios n).v == v)
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_system_const v ios (n - 1)

(* Concrete extensional law for constant systems. *)
let stream_of_output_system_const
  (#input #result: Type)
  (v: result)
  (ios: io_stream input None)
  : Lemma
    (ensures
      ES.eq
        (stream_of_output (system_const v) ios)
        (ES.const v))
  =
  introduce forall (n: nat).
    stream_of_output (system_const v) ios n == ES.const v n
  with (
    lemma_step_result_at_system_const v ios n
  )

(*** system_mu ***)

(* The recursive value guessed by the oracle at each step: [system_mu] adds a
   [Some value] oracle component whose per-step value becomes the output. *)
let mu_guess
  (#input #value: Type)
  (#oracle: option Type)
  (ios: io_stream input (Some value `type_join` oracle))
  : E.stream value
  =
  fun n -> type_join_fst #(Some value) #oracle (snd (ios n))

(* The io-stream that [system_mu t1] feeds to its body [t1]: the guessed value
   paired with the source input, and the remaining oracle component. *)
let mu_body_ios
  (#input #value: Type)
  (#oracle: option Type)
  (ios: io_stream input (Some value `type_join` oracle))
  : io_stream (value & input) oracle
  =
  fun n ->
    ((mu_guess ios n, fst (ios n)), type_join_snd #(Some value) #oracle (snd (ios n)))

(* Step-indexed alignment for [system_mu]: its state and checks are exactly the
   body's run on [mu_body_ios], with the output overridden by the guess and an
   assumption tying the guess to the body's output. *)
let rec lemma_step_result_at_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: system (value & input) oracle state value)
  (ios: io_stream input (Some value `type_join` oracle))
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (system_mu t1) ios n).s ==
        (step_result_at t1 (mu_body_ios ios) n).s /\
      (step_result_at (system_mu t1) ios n).v == mu_guess ios n /\
      (step_result_at (system_mu t1) ios n).chck ==
        (checks_assumption
          (mu_guess ios n == (step_result_at t1 (mu_body_ios ios) n).v)
          `checks_join` (step_result_at t1 (mu_body_ios ios) n).chck))
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_system_mu t1 ios (n - 1)

(* [system_mu] outputs the oracle-guessed recursive value. *)
let lemma_stream_of_output_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: system (value & input) oracle state value)
  (ios: io_stream input (Some value `type_join` oracle))
  (n: nat)
  : Lemma
    (ensures stream_of_output (system_mu t1) ios n == mu_guess ios n)
  =
  lemma_step_result_at_system_mu t1 ios n

(* [system_mu] obligations are exactly the body's obligations. *)
let lemma_stream_of_obligations_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: system (value & input) oracle state value)
  (ios: io_stream input (Some value `type_join` oracle))
  (n: nat)
  : Lemma
    (ensures
      stream_of_obligations (system_mu t1) ios n ==
        stream_of_obligations t1 (mu_body_ios ios) n)
  =
  lemma_step_result_at_system_mu t1 ios n

(* [system_mu] assumptions are the body's assumptions together with the tie
   between the guessed value and the body's output. *)
let lemma_stream_of_assumptions_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: system (value & input) oracle state value)
  (ios: io_stream input (Some value `type_join` oracle))
  (n: nat)
  : Lemma
    (ensures
      (stream_of_assumptions (system_mu t1) ios n <==>
        ((mu_guess ios n == stream_of_output t1 (mu_body_ios ios) n) /\
         stream_of_assumptions t1 (mu_body_ios ios) n)))
  =
  lemma_step_result_at_system_mu t1 ios n

(*** Prefix congruence ***)

(* [step_result_at t j n] depends only on the io-stream prefix [j 0 .. j n], so
   io-streams agreeing up to [n] yield the same step result. *)
let rec lemma_step_result_at_congruence
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (j1 j2: io_stream input oracle)
  (n: nat)
  : Lemma
    (requires (forall (k: nat). k <= n ==> j1 k == j2 k))
    (ensures step_result_at t j1 n == step_result_at t j2 n)
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_congruence t j1 j2 (n - 1)

(* Output stream at [n] depends only on the io-stream prefix up to [n]. *)
let lemma_stream_of_output_congruence
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (j1 j2: io_stream input oracle)
  (n: nat)
  : Lemma
    (requires (forall (k: nat). k <= n ==> j1 k == j2 k))
    (ensures stream_of_output t j1 n == stream_of_output t j2 n)
  =
  lemma_step_result_at_congruence t j1 j2 n

(* Assumptions stream at [n] depends only on the io-stream prefix up to [n]. *)
let lemma_stream_of_assumptions_congruence
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (j1 j2: io_stream input oracle)
  (n: nat)
  : Lemma
    (requires (forall (k: nat). k <= n ==> j1 k == j2 k))
    (ensures stream_of_assumptions t j1 n == stream_of_assumptions t j2 n)
  =
  lemma_step_result_at_congruence t j1 j2 n

(* Obligations stream at [n] depends only on the io-stream prefix up to [n]. *)
let lemma_stream_of_obligations_congruence
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (j1 j2: io_stream input oracle)
  (n: nat)
  : Lemma
    (requires (forall (k: nat). k <= n ==> j1 k == j2 k))
    (ensures stream_of_obligations t j1 n == stream_of_obligations t j2 n)
  =
  lemma_step_result_at_congruence t j1 j2 n
