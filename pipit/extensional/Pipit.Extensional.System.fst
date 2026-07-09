(* Extensional stream semantics for transition systems.

   This module provides stream projections of a system's observable behavior,
   an oracle/state-hiding system package, and the [mu] recursion combinator.

   Observational-equivalence predicates live in [Pipit.Extensional.System.Eq];
   the [system_let] / [system_const] laws are gathered in a section at the end.
*)
module Pipit.Extensional.System

module E = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module EPS = Pipit.Extensional.PStream
module SB = Pipit.System.Base

(* Input stream consumed by a system step-by-step. *)
type io_stream (input: Type) (oracle: option Type) =
  E.stream (input & SB.option_type_sem oracle)

(* Execute exactly n+1 steps and return the final step result.
   n = 0 corresponds to one step from init using ios 0. *)
let rec step_result_at
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  (n: nat)
  : Tot (SB.step_result state result)
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
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  : E.pstream result
  =
  fun n ->
    let stp = step_result_at t ios n in
    {
      pv = stp.v;
      pasm = SB.option_prop_sem stp.chck.assumptions;
      pobl = SB.option_prop_sem stp.chck.obligations;
    }

(* Observable output stream. *)
let stream_of_output
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  : E.stream result
  =
  EPS.values (pstream_of_system t ios)

(* Observable assumptions stream: did assumptions hold at each step? *)
let stream_of_assumptions
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  : E.stream prop
  =
  EPS.assumptions (pstream_of_system t ios)

(* Observable obligations stream: were obligations satisfied at each step? *)
let stream_of_obligations
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  : E.stream prop
  =
  EPS.obligations (pstream_of_system t ios)

(*** Oracle/state-hiding system package ***)

(* A transition system with its oracle and state types hidden.

   Hiding [oracle] and [state] lets clients present a system uniformly as
   [sys input output]. [state] disappears observably (it is threaded away by
   [stream_of_output]); [oracle] hides as a type, but its per-step values must
   still be quantified by the client. *)
noeq
type sys (input output: Type) = {
  oracle: option Type;
  state:  option Type;
  raw:    SB.system input oracle state output;
}

(* Pair an input stream with an oracle stream into the io-stream consumed by
   the underlying system. *)
let with_oracle
  (#input #output: Type)
  (t: sys input output)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem t.oracle))
  : io_stream input t.oracle
  =
  fun n -> (is n, orc n)

(* Observable output stream of [t] on input stream [is] under oracle [orc]. *)
let outputs
  (#input #output: Type)
  (t: sys input output)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem t.oracle))
  : E.stream output
  =
  stream_of_output t.raw (with_oracle t is orc)

(* Recursive knot as a system combinator: [system_mu] hides the extra oracle
   component (the guessed recursive value) and the body state. *)
let mu
  (#input #output: Type)
  (body: sys (output & input) output)
  : sys input output
  =
  {
    oracle = SB.type_join (Some output) body.oracle;
    state  = body.state;
    raw    = SB.system_mu body.raw;
  }

(*** Pointwise combinators: id / map / fby ***)

(* Identity system: output equals the input. *)
let id (#input: Type) : sys input input =
  { oracle = None; state = None; raw = SB.system_project (fun i -> i) }

(* Map a pure function over a system's output. *)
let map
  (#input #output1 #output2: Type)
  (f: output1 -> output2)
  (t: sys input output1)
  : sys input output2
  =
  { oracle = t.oracle; state = t.state; raw = SB.system_map_result f t.raw }

(* [v0 fby t]: emit [v0] at step 0, then the previous output of [t]. Only the
   output is delayed; the checks are [t]'s at the current step. *)
let fby
  (#input #output: Type)
  (v0: output)
  (t: sys input output)
  : sys input output
  =
  { oracle = t.oracle; state = SB.type_join (Some output) t.state; raw = SB.system_pre v0 t.raw }

(* Laws relating the observable streams of these combinators to their operands.
   PROOFS DEFERRED: each is a straightforward induction on [step_result_at],
   like the [system_mu] alignment lemmas. *)

(* [system_project f] outputs [f] of the current input; no checks. *)
let lemma_system_project
  (#input #result: Type)
  (f: input -> result)
  (ios: io_stream input None)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (SB.system_project f) ios n == f (fst (ios n)) /\
      stream_of_assumptions (SB.system_project f) ios n == True /\
      stream_of_obligations (SB.system_project f) ios n == True)
  =
  admit ()

(* [system_map_result f] maps the output and preserves the checks. *)
let lemma_system_map_result
  (#input #result #result': Type)
  (#oracle #state: option Type)
  (f: result -> result')
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (SB.system_map_result f t) ios n == f (stream_of_output t ios n) /\
      stream_of_assumptions (SB.system_map_result f t) ios n == stream_of_assumptions t ios n /\
      stream_of_obligations (SB.system_map_result f t) ios n == stream_of_obligations t ios n)
  =
  admit ()

(* [system_pre v0 t] delays the output by one step (an [fby]); checks stay at
   the current step. *)
let lemma_system_pre
  (#input #value: Type)
  (#oracle #state: option Type)
  (v0: value)
  (t: SB.system input oracle state value)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (SB.system_pre v0 t) ios n == ES.fby v0 (stream_of_output t ios) n /\
      stream_of_assumptions (SB.system_pre v0 t) ios n == stream_of_assumptions t ios n /\
      stream_of_obligations (SB.system_pre v0 t) ios n == stream_of_obligations t ios n)
  =
  admit ()

(*** system_mu ***)

(* The recursive value guessed by the oracle at each step: [system_mu] adds a
   [Some value] oracle component whose per-step value becomes the output. *)
let mu_guess
  (#input #value: Type)
  (#oracle: option Type)
  (ios: io_stream input (SB.type_join (Some value) oracle))
  : E.stream value
  =
  fun n -> SB.type_join_fst #(Some value) #oracle (snd (ios n))

(* The io-stream that [system_mu t1] feeds to its body [t1]: the guessed value
   paired with the source input, and the remaining oracle component. *)
let mu_body_ios
  (#input #value: Type)
  (#oracle: option Type)
  (ios: io_stream input (SB.type_join (Some value) oracle))
  : io_stream (value & input) oracle
  =
  fun n ->
    ((mu_guess ios n, fst (ios n)), SB.type_join_snd #(Some value) #oracle (snd (ios n)))

(* Step-indexed alignment for [system_mu]: its state and checks are exactly the
   body's run on [mu_body_ios], with the output overridden by the guess and an
   assumption tying the guess to the body's output. *)
let rec lemma_step_result_at_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: SB.system (value & input) oracle state value)
  (ios: io_stream input (SB.type_join (Some value) oracle))
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (SB.system_mu t1) ios n).s ==
        (step_result_at t1 (mu_body_ios ios) n).s /\
      (step_result_at (SB.system_mu t1) ios n).v == mu_guess ios n /\
      (step_result_at (SB.system_mu t1) ios n).chck ==
        (SB.checks_join
          (SB.checks_assumption
            (mu_guess ios n == (step_result_at t1 (mu_body_ios ios) n).v))
          (step_result_at t1 (mu_body_ios ios) n).chck))
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_system_mu t1 ios (n - 1)

(* [system_mu] outputs the oracle-guessed recursive value. *)
let lemma_stream_of_output_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: SB.system (value & input) oracle state value)
  (ios: io_stream input (SB.type_join (Some value) oracle))
  (n: nat)
  : Lemma
    (ensures stream_of_output (SB.system_mu t1) ios n == mu_guess ios n)
  =
  lemma_step_result_at_system_mu t1 ios n

(* [system_mu] obligations are exactly the body's obligations. *)
let lemma_stream_of_obligations_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: SB.system (value & input) oracle state value)
  (ios: io_stream input (SB.type_join (Some value) oracle))
  (n: nat)
  : Lemma
    (ensures
      stream_of_obligations (SB.system_mu t1) ios n ==
        stream_of_obligations t1 (mu_body_ios ios) n)
  =
  lemma_step_result_at_system_mu t1 ios n

(* [system_mu] assumptions are the body's assumptions together with the tie
   between the guessed value and the body's output. *)
let lemma_stream_of_assumptions_system_mu
  (#input #value: Type)
  (#oracle #state: option Type)
  (t1: SB.system (value & input) oracle state value)
  (ios: io_stream input (SB.type_join (Some value) oracle))
  (n: nat)
  : Lemma
    (ensures
      (stream_of_assumptions (SB.system_mu t1) ios n <==>
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
  (t: SB.system input oracle state result)
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
  (t: SB.system input oracle state result)
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
  (t: SB.system input oracle state result)
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
  (t: SB.system input oracle state result)
  (j1 j2: io_stream input oracle)
  (n: nat)
  : Lemma
    (requires (forall (k: nat). k <= n ==> j1 k == j2 k))
    (ensures stream_of_obligations t j1 n == stream_of_obligations t j2 n)
  =
  lemma_step_result_at_congruence t j1 j2 n

(*** [system_let] and [system_const] laws ***)

(* Split the oracle/input stream used by [system_let] into the left
   component consumed by [t1]. *)
let let_ios_left
  (#input: Type)
  (#oracle1 #oracle2: option Type)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  : io_stream input oracle1
  =
  fun n ->
    let io = ios n in
    (fst io, SB.type_join_fst (snd io))

(* Build the right-component input stream consumed by [t2], given an
   extension function and a stream of values from [t1]. *)
let let_ios_right
  (#input #input' #v1: Type)
  (#oracle1 #oracle2: option Type)
  (extend: input -> v1 -> input')
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  (x: E.stream v1)
  : io_stream input' oracle2
  =
  fun n ->
    let io = ios n in
    (extend (fst io) (x n), SB.type_join_snd (snd io))

(* Step-indexed alignment for [system_let]: the right state/output match
   running [t2] on the stream extended with [t1]'s outputs. *)
let rec lemma_step_result_at_system_let
  (#input #input' #v1 #v2: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (extend: input -> v1 -> input')
  (t1: SB.system input oracle1 state1 v1)
  (t2: SB.system input' oracle2 state2 v2)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  (n: nat)
  : Lemma
    (ensures
      SB.type_join_fst (step_result_at (SB.system_let extend t1 t2) ios n).s ==
      (step_result_at t1 (let_ios_left ios) n).s /\
      SB.type_join_snd (step_result_at (SB.system_let extend t1 t2) ios n).s ==
      (step_result_at t2
        (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))
        n).s /\
      (step_result_at (SB.system_let extend t1 t2) ios n).v ==
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
  (t1: SB.system input oracle1 state1 v1)
  (t2: SB.system input' oracle2 state2 v2)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  : Lemma
    (ensures
      ES.eq
        (stream_of_output (SB.system_let extend t1 t2) ios)
        (stream_of_output t2
          (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))))
  =
  introduce forall (n: nat).
    stream_of_output (SB.system_let extend t1 t2) ios n ==
    stream_of_output t2
      (let_ios_right extend ios (stream_of_output t1 (let_ios_left ios)))
      n
  with (
    lemma_step_result_at_system_let extend t1 t2 ios n
  )

(* Step-indexed execution of [system_const] always returns the same value. *)
let rec lemma_step_result_at_system_const
  (#input #result: Type)
  (v: result)
  (ios: io_stream input None)
  (n: nat)
  : Lemma
    (ensures (step_result_at (SB.system_const v) ios n).v == v)
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
        (stream_of_output (SB.system_const v) ios)
        (ES.const v))
  =
  introduce forall (n: nat).
    stream_of_output (SB.system_const v) ios n == ES.const v n
  with (
    lemma_step_result_at_system_const v ios n
  )
