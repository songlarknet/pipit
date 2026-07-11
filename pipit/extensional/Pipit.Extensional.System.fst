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

(* Project a joined-oracle io-stream onto its two components (for [system_ap]). *)
unfold
let io_fst
  (#input: Type) (#oracle1 #oracle2: option Type)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  : io_stream input oracle1
  =
  fun n -> (fst (ios n), SB.type_join_fst #oracle1 #oracle2 (snd (ios n)))

unfold
let io_snd
  (#input: Type) (#oracle1 #oracle2: option Type)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  : io_stream input oracle2
  =
  fun n -> (fst (ios n), SB.type_join_snd #oracle1 #oracle2 (snd (ios n)))

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

(*** Applicative structure: pure / ap, with map (<$>) derived ***)

(* [pure v] emits [v] at every step, ignoring the input — the applicative unit. *)
let pure (#input #output: Type) (v: output) : sys input output =
  { oracle = None; state = None; raw = SB.system_const v }

(* Constant system, an alias of [pure]. *)
let const (#input #output: Type) (v: output) : sys input output = pure v

(* Applicative apply (<*>): run [tf] and [ta] in lock-step on the same input and
   apply [tf]'s function output to [ta]'s argument output. *)
let ap
  (#input #a #b: Type)
  (tf: sys input (a -> b))
  (ta: sys input a)
  : sys input b
  =
  {
    oracle = SB.type_join tf.oracle ta.oracle;
    state  = SB.type_join tf.state ta.state;
    raw    = SB.system_ap tf.raw ta.raw;
  }

(* Map a pure function over a system's output (<$>), derived from the applicative
   primitives: [map f t = pure f <*> t]. *)
let map
  (#input #output1 #output2: Type)
  (f: output1 -> output2)
  (t: sys input output1)
  : sys input output2
  =
  ap (pure f) t

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
   Each is a step-indexed induction on [step_result_at], like the [system_mu]
   alignment lemmas, lifted to the observable streams. *)

(* [system_project f] is stateless: it outputs [f] of the current input with no
   checks. *)
let rec lemma_step_result_at_system_project
  (#input #result: Type)
  (f: input -> result)
  (ios: io_stream input None)
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (SB.system_project f) ios n).v == f (fst (ios n)) /\
      (step_result_at (SB.system_project f) ios n).chck == SB.checks_none)
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_system_project f ios (n - 1)

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
  lemma_step_result_at_system_project f ios n

(* [system_map_result f] keeps the state and checks, mapping only the output. *)
let rec lemma_step_result_at_system_map_result
  (#input #result #result': Type)
  (#oracle #state: option Type)
  (f: result -> result')
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (SB.system_map_result f t) ios n).s == (step_result_at t ios n).s /\
      (step_result_at (SB.system_map_result f t) ios n).v == f (step_result_at t ios n).v /\
      (step_result_at (SB.system_map_result f t) ios n).chck == (step_result_at t ios n).chck)
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_system_map_result f t ios (n - 1)

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
  lemma_step_result_at_system_map_result f t ios n

(* [type_join_fst]/[type_join_snd] invert [type_join_tup]. *)
let lemma_type_join_fst_tup
  (#t1 #t2: option Type)
  (a: SB.option_type_sem t1)
  (b: SB.option_type_sem t2)
  : Lemma
    (SB.type_join_fst #t1 #t2 (SB.type_join_tup #t1 #t2 a b) == a)
  =
  match t1, t2 with | Some _, Some _ -> () | None, _ -> () | _, None -> ()

let lemma_type_join_snd_tup
  (#t1 #t2: option Type)
  (a: SB.option_type_sem t1)
  (b: SB.option_type_sem t2)
  : Lemma
    (SB.type_join_snd #t1 #t2 (SB.type_join_tup #t1 #t2 a b) == b)
  =
  match t1, t2 with | Some _, Some _ -> () | None, _ -> () | _, None -> ()

(* [system_ap tf ta] runs both operands in lock-step; its step result is [tf]'s
   function applied to [ta]'s argument, the joined states, and conjoined checks.
   The operands see the oracle projections [io_fst]/[io_snd]. *)
#push-options "--split_queries always"
let rec lemma_step_result_at_system_ap
  (#input #a #b: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (tf: SB.system input oracle1 state1 (a -> b))
  (ta: SB.system input oracle2 state2 a)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  (n: nat)
  : Lemma
    (ensures (
      let apr = step_result_at (SB.system_ap tf ta) ios n in
      let fr  = step_result_at tf (io_fst ios) n in
      let ar  = step_result_at ta (io_snd ios) n in
      apr.v == fr.v ar.v /\
      apr.s == SB.type_join_tup #state1 #state2 fr.s ar.s /\
      apr.chck == SB.checks_join fr.chck ar.chck))
    (decreases n)
  =
  match n with
  | 0 ->
    lemma_type_join_fst_tup #state1 #state2 tf.init ta.init;
    lemma_type_join_snd_tup #state1 #state2 tf.init ta.init;
    (* Splitting the three-conjunct post per component keeps Z3 from timing out
       on the joined step term. *)
    assert ((step_result_at (SB.system_ap tf ta) ios 0).v ==
            (step_result_at tf (io_fst ios) 0).v (step_result_at ta (io_snd ios) 0).v);
    assert ((step_result_at (SB.system_ap tf ta) ios 0).s ==
            SB.type_join_tup #state1 #state2 (step_result_at tf (io_fst ios) 0).s (step_result_at ta (io_snd ios) 0).s);
    assert ((step_result_at (SB.system_ap tf ta) ios 0).chck ==
            SB.checks_join (step_result_at tf (io_fst ios) 0).chck (step_result_at ta (io_snd ios) 0).chck)
  | _ ->
    lemma_step_result_at_system_ap tf ta ios (n - 1);
    lemma_type_join_fst_tup #state1 #state2
      (step_result_at tf (io_fst ios) (n - 1)).s (step_result_at ta (io_snd ios) (n - 1)).s;
    lemma_type_join_snd_tup #state1 #state2
      (step_result_at tf (io_fst ios) (n - 1)).s (step_result_at ta (io_snd ios) (n - 1)).s

let lemma_system_ap
  (#input #a #b: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (tf: SB.system input oracle1 state1 (a -> b))
  (ta: SB.system input oracle2 state2 a)
  (ios: io_stream input (SB.type_join oracle1 oracle2))
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (SB.system_ap tf ta) ios n ==
        (stream_of_output tf (io_fst ios) n) (stream_of_output ta (io_snd ios) n) /\
      (stream_of_assumptions (SB.system_ap tf ta) ios n <==>
        (stream_of_assumptions tf (io_fst ios) n /\ stream_of_assumptions ta (io_snd ios) n)) /\
      (stream_of_obligations (SB.system_ap tf ta) ios n <==>
        (stream_of_obligations tf (io_fst ios) n /\ stream_of_obligations ta (io_snd ios) n)))
  =
  lemma_step_result_at_system_ap tf ta ios n
#pop-options

(* Sys-package-level [ap] law: the same as [lemma_system_ap] but phrased over
   [(ap tf ta).raw], so callers connect through the [sys] combinator without
   having to delta-unfold [ap] to expose the raw [system_ap]. *)
let lemma_ap
  (#input #a #b: Type)
  (tf: sys input (a -> b))
  (ta: sys input a)
  (ios: io_stream input (ap tf ta).oracle)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (ap tf ta).raw ios n ==
        (stream_of_output tf.raw (io_fst ios) n) (stream_of_output ta.raw (io_snd ios) n) /\
      (stream_of_assumptions (ap tf ta).raw ios n <==>
        (stream_of_assumptions tf.raw (io_fst ios) n /\ stream_of_assumptions ta.raw (io_snd ios) n)) /\
      (stream_of_obligations (ap tf ta).raw ios n <==>
        (stream_of_obligations tf.raw (io_fst ios) n /\ stream_of_obligations ta.raw (io_snd ios) n)))
  =
  lemma_system_ap tf.raw ta.raw ios n

(* Derived law for [map f t = pure f <*> t]. Because [pure]'s oracle and state
   are [None], the join projections reduce definitionally and [system_ap
   (system_const f) t] behaves exactly like the old [system_map_result f t]:
   the output is [f] of [t]'s, and the checks are unchanged. *)
let rec lemma_step_result_at_map
  (#input #result #result': Type)
  (#oracle #state: option Type)
  (f: result -> result')
  (t: SB.system input oracle state result)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures (
      let apr = step_result_at (SB.system_ap (SB.system_const f) t) ios n in
      let tr  = step_result_at t ios n in
      apr.s == tr.s /\ apr.v == f tr.v /\ apr.chck == tr.chck))
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ -> lemma_step_result_at_map f t ios (n - 1)

let lemma_map
  (#input #result #result': Type)
  (f: result -> result')
  (t: sys input result)
  (ios: io_stream input (map f t).oracle)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (map f t).raw ios n == f (stream_of_output t.raw ios n) /\
      stream_of_assumptions (map f t).raw ios n == stream_of_assumptions t.raw ios n /\
      stream_of_obligations (map f t).raw ios n == stream_of_obligations t.raw ios n)
  =
  lemma_step_result_at_map f t.raw ios n

(* [system_pre v0 t] carries [t]'s current step in its state (first component the
   output, second the [t]-state), emitting the previous output; checks are [t]'s
   at the current step. *)
let rec lemma_step_result_at_system_pre
  (#input #value: Type)
  (#oracle #state: option Type)
  (v0: value)
  (t: SB.system input oracle state value)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (SB.system_pre v0 t) ios n).chck == (step_result_at t ios n).chck /\
      (step_result_at (SB.system_pre v0 t) ios n).s ==
        SB.type_join_tup #(Some value) #state
          (step_result_at t ios n).v (step_result_at t ios n).s /\
      (step_result_at (SB.system_pre v0 t) ios n).v ==
        (if n = 0 then v0 else (step_result_at t ios (n - 1)).v))
    (decreases n)
  =
  match n with
  | 0 -> ()
  | _ ->
    lemma_step_result_at_system_pre v0 t ios (n - 1);
    lemma_type_join_fst_tup #(Some value) #state
      (step_result_at t ios (n - 1)).v (step_result_at t ios (n - 1)).s;
    lemma_type_join_snd_tup #(Some value) #state
      (step_result_at t ios (n - 1)).v (step_result_at t ios (n - 1)).s

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
  lemma_step_result_at_system_pre v0 t ios n

(*** Oracle-free recursion: mufby ***)

(* Recursion with a built-in [fby] delay. The feedback given to [body] is the
   *previous* output, carried in state (initialised to [v0]) — so, unlike
   [system_mu], no oracle guess is needed. [system_mufby v0 body] computes the
   [os] with [os == body (v0 fby os, input)]. *)
let system_mufby
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  : SB.system input oracle (SB.type_join state (Some output)) output
  =
  {
    init = SB.type_join_tup #state #(Some output) body.init v0;
    step = (fun i o s ->
      let bs = SB.type_join_fst #state #(Some output) s in
      let fb = SB.type_join_snd #state #(Some output) s in
      let stp = body.step (fb, i) o bs in
      {
        s = SB.type_join_tup #state #(Some output) stp.s stp.v;
        v = stp.v;
        chck = stp.chck;
      });
  }

(* Oracle-free recursion combinator on the [sys] package. Because it introduces
   no oracle, its observable streams are functions of the input alone (hence
   causal by construction), so it may be used in specifications. *)
let mufby
  (#input #output: Type)
  (v0: output)
  (body: sys (output & input) output)
  : sys input output
  =
  {
    oracle = body.oracle;
    state  = SB.type_join body.state (Some output);
    raw    = system_mufby v0 body.raw;
  }

(* The io-stream [system_mufby v0 body] feeds to [body]: the delayed output
   [v0 fby os] as feedback, with the original source input and oracle. *)
let mufby_body_ios
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  (ios: io_stream input oracle)
  : io_stream (output & input) oracle
  =
  fun n ->
    ((ES.fby v0 (stream_of_output (system_mufby v0 body) ios) n, fst (ios n)), snd (ios n))

(* Alignment: [system_mufby v0 body] runs [body] on [mufby_body_ios], storing the
   current output as the next feedback. *)
let rec lemma_step_result_at_system_mufby
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (system_mufby v0 body) ios n).v ==
        (step_result_at body (mufby_body_ios v0 body ios) n).v /\
      (step_result_at (system_mufby v0 body) ios n).chck ==
        (step_result_at body (mufby_body_ios v0 body ios) n).chck /\
      SB.type_join_fst #state #(Some output)
        (step_result_at (system_mufby v0 body) ios n).s ==
        (step_result_at body (mufby_body_ios v0 body ios) n).s /\
      SB.type_join_snd #state #(Some output)
        (step_result_at (system_mufby v0 body) ios n).s ==
        (step_result_at (system_mufby v0 body) ios n).v)
    (decreases n)
  =
  (match n with
   | 0 -> ()
   | _ -> lemma_step_result_at_system_mufby v0 body ios (n - 1));
  lemma_type_join_fst_tup #state #(Some output)
    (step_result_at body (mufby_body_ios v0 body ios) n).s
    (step_result_at body (mufby_body_ios v0 body ios) n).v;
  lemma_type_join_snd_tup #state #(Some output)
    (step_result_at body (mufby_body_ios v0 body ios) n).s
    (step_result_at body (mufby_body_ios v0 body ios) n).v

(* Observable [mufby] unfold: its output/checks are [body]'s run on the
   [v0 fby os]-feedback io-stream. *)
let lemma_system_mufby
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  (ios: io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (system_mufby v0 body) ios n ==
        stream_of_output body (mufby_body_ios v0 body ios) n /\
      stream_of_assumptions (system_mufby v0 body) ios n ==
        stream_of_assumptions body (mufby_body_ios v0 body ios) n /\
      stream_of_obligations (system_mufby v0 body) ios n ==
        stream_of_obligations body (mufby_body_ios v0 body ios) n)
  =
  lemma_step_result_at_system_mufby v0 body ios n

(*** delayed_body: the mu-body realising mufby via a guessed feedback ***)

(* [system_delayed_body v0 body] is a [mu]-body: it takes [(guess, input)],
   feeds [body] the *delayed* guess [v0 fby guess] as feedback (carried in
   state, initialised to [v0]) together with [input]. Running it under
   [system_mu] and tying [guess == output] reproduces [system_mufby]. *)
let system_delayed_body
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  : SB.system (output & input) oracle (SB.type_join state (Some output)) output
  =
  {
    init = SB.type_join_tup #state #(Some output) body.init v0;
    step = (fun i o s ->
      let bs = SB.type_join_fst #state #(Some output) s in
      let fb = SB.type_join_snd #state #(Some output) s in
      let stp = body.step (fb, snd i) o bs in
      {
        s = SB.type_join_tup #state #(Some output) stp.s (fst i);
        v = stp.v;
        chck = stp.chck;
      });
  }

(* The io-stream [system_delayed_body v0 body] feeds to [body]: the delayed
   guess [v0 fby (fst-of-input)] as feedback, the real input, and the oracle. *)
let delayed_body_ios
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  (ios: io_stream (output & input) oracle)
  : io_stream (output & input) oracle
  =
  fun n ->
    ((ES.fby v0 (fun m -> fst (fst (ios m))) n, snd (fst (ios n))), snd (ios n))

(* Alignment: [system_delayed_body v0 body] runs [body] on [delayed_body_ios],
   storing the current guess as the next feedback. *)
let rec lemma_step_result_at_system_delayed_body
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  (ios: io_stream (output & input) oracle)
  (n: nat)
  : Lemma
    (ensures
      (step_result_at (system_delayed_body v0 body) ios n).v ==
        (step_result_at body (delayed_body_ios v0 body ios) n).v /\
      (step_result_at (system_delayed_body v0 body) ios n).chck ==
        (step_result_at body (delayed_body_ios v0 body ios) n).chck /\
      SB.type_join_fst #state #(Some output)
        (step_result_at (system_delayed_body v0 body) ios n).s ==
        (step_result_at body (delayed_body_ios v0 body ios) n).s /\
      SB.type_join_snd #state #(Some output)
        (step_result_at (system_delayed_body v0 body) ios n).s ==
        fst (fst (ios n)))
    (decreases n)
  =
  (match n with
   | 0 -> ()
   | _ -> lemma_step_result_at_system_delayed_body v0 body ios (n - 1));
  lemma_type_join_fst_tup #state #(Some output)
    (step_result_at body (delayed_body_ios v0 body ios) n).s
    (fst (fst (ios n)));
  lemma_type_join_snd_tup #state #(Some output)
    (step_result_at body (delayed_body_ios v0 body ios) n).s
    (fst (fst (ios n)))

(* Observable [delayed_body] unfold: output/checks equal [body]'s run on
   [delayed_body_ios]. *)
let lemma_system_delayed_body
  (#input #output: Type)
  (#oracle #state: option Type)
  (v0: output)
  (body: SB.system (output & input) oracle state output)
  (ios: io_stream (output & input) oracle)
  (n: nat)
  : Lemma
    (ensures
      stream_of_output (system_delayed_body v0 body) ios n ==
        stream_of_output body (delayed_body_ios v0 body ios) n /\
      stream_of_assumptions (system_delayed_body v0 body) ios n ==
        stream_of_assumptions body (delayed_body_ios v0 body ios) n /\
      stream_of_obligations (system_delayed_body v0 body) ios n ==
        stream_of_obligations body (delayed_body_ios v0 body ios) n)
  =
  lemma_step_result_at_system_delayed_body v0 body ios n

(* [delayed_body] as a [sys] package: the [mu]-body that, run under [mu] with the
   guess tied to the output, reproduces [mufby v0 body]. *)
let delayed_body
  (#input #output: Type)
  (v0: output)
  (body: sys (output & input) output)
  : sys (output & input) output
  =
  {
    oracle = body.oracle;
    state  = SB.type_join body.state (Some output);
    raw    = system_delayed_body v0 body.raw;
  }

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

(*** Contract: internalise a pre/post into a system's checks ***)

(* [system_contract p t q] runs the program [t], the precondition [p] on the
   input, and the postcondition [q] on the paired input & [t]-output. It emits
   [t]'s output and threads all three systems' own checks, plus assumes [p]'s
   value ([checks_assumption]) and asserts [q]'s value ([checks_obligation]).

   This is the internalisation used by the [contract]-bridge rule: a triple
   [{ p } t { q }] becomes validity of [system_contract p t q] (its assumptions
   entail its obligations), which can then be rewritten via [equiv]. *)
let system_contract
  (#input #output: Type)
  (#op #ot #oq #sp #st #sq: option Type)
  (p: SB.system input op sp prop)
  (t: SB.system input ot st output)
  (q: SB.system (input & output) oq sq prop)
  : SB.system input
      (SB.type_join op (SB.type_join ot oq))
      (SB.type_join sp (SB.type_join st sq))
      output
  =
  {
    init = SB.type_join_tup #sp #(SB.type_join st sq) p.init
             (SB.type_join_tup #st #sq t.init q.init);
    step = (fun i o s ->
      let o_p = SB.type_join_fst #op #(SB.type_join ot oq) o in
      let o'  = SB.type_join_snd #op #(SB.type_join ot oq) o in
      let o_t = SB.type_join_fst #ot #oq o' in
      let o_q = SB.type_join_snd #ot #oq o' in
      let s_p = SB.type_join_fst #sp #(SB.type_join st sq) s in
      let s'  = SB.type_join_snd #sp #(SB.type_join st sq) s in
      let s_t = SB.type_join_fst #st #sq s' in
      let s_q = SB.type_join_snd #st #sq s' in
      let rt = t.step i o_t s_t in
      let rp = p.step i o_p s_p in
      let rq = q.step (i, rt.v) o_q s_q in
      {
        s = SB.type_join_tup #sp #(SB.type_join st sq) rp.s
              (SB.type_join_tup #st #sq rt.s rq.s);
        v = rt.v;
        chck = SB.checks_assumption rp.v `SB.checks_join`
               SB.checks_obligation rq.v `SB.checks_join`
               rp.chck `SB.checks_join` rt.chck `SB.checks_join` rq.chck;
      });
  }

(* The io-stream [system_contract p t q] feeds to the precondition [p]: the
   source input and the [p]-oracle projection. *)
let contract_ios_p
  (#input #output: Type)
  (#op #ot #oq: option Type)
  (ios: io_stream input (SB.type_join op (SB.type_join ot oq)))
  : io_stream input op
  =
  fun n -> (fst (ios n), SB.type_join_fst #op #(SB.type_join ot oq) (snd (ios n)))

(* The io-stream [system_contract p t q] feeds to the program [t]. *)
let contract_ios_t
  (#input #output: Type)
  (#op #ot #oq: option Type)
  (ios: io_stream input (SB.type_join op (SB.type_join ot oq)))
  : io_stream input ot
  =
  fun n ->
    (fst (ios n),
     SB.type_join_fst #ot #oq (SB.type_join_snd #op #(SB.type_join ot oq) (snd (ios n))))

(* The io-stream [system_contract p t q] feeds to the postcondition [q]: the
   source input paired with [t]'s output, and the [q]-oracle projection. *)
let contract_ios_q
  (#input #output: Type)
  (#op #ot #oq #st: option Type)
  (t: SB.system input ot st output)
  (ios: io_stream input (SB.type_join op (SB.type_join ot oq)))
  : io_stream (input & output) oq
  =
  fun n ->
    ((fst (ios n), stream_of_output t (contract_ios_t #input #output #op #ot #oq ios) n),
     SB.type_join_snd #ot #oq (SB.type_join_snd #op #(SB.type_join ot oq) (snd (ios n))))

(* Contract as a [sys] package: internalises [p]/[q] into [t]'s checks. *)
let contract
  (#input #output: Type)
  (p: sys input prop)
  (t: sys input output)
  (q: sys (input & output) prop)
  : sys input output
  =
  {
    oracle = SB.type_join p.oracle (SB.type_join t.oracle q.oracle);
    state  = SB.type_join p.state (SB.type_join t.state q.state);
    raw    = system_contract p.raw t.raw q.raw;
  }

(* Step-indexed alignment for [system_contract]: it runs [p]/[t]/[q] on their
   projected io-streams, emits [t]'s output, joins their states, and its checks
   are [t]'s output-assumption on [p], output-obligation on [q], and all three
   subsystems' own checks. *)
#push-options "--split_queries always --z3rlimit 60"
let rec lemma_step_result_at_system_contract
  (#input #output: Type)
  (#op #ot #oq #sp #st #sq: option Type)
  (p: SB.system input op sp prop)
  (t: SB.system input ot st output)
  (q: SB.system (input & output) oq sq prop)
  (ios: io_stream input (SB.type_join op (SB.type_join ot oq)))
  (n: nat)
  : Lemma
    (ensures (
      let cr = step_result_at (system_contract p t q) ios n in
      let pr = step_result_at p (contract_ios_p #input #output #op #ot #oq ios) n in
      let tr = step_result_at t (contract_ios_t #input #output #op #ot #oq ios) n in
      let qr = step_result_at q (contract_ios_q #input #output #op #ot #oq #st t ios) n in
      cr.v == tr.v /\
      cr.s == SB.type_join_tup #sp #(SB.type_join st sq) pr.s
                (SB.type_join_tup #st #sq tr.s qr.s) /\
      cr.chck == (SB.checks_assumption pr.v `SB.checks_join`
                  SB.checks_obligation qr.v `SB.checks_join`
                  pr.chck `SB.checks_join` tr.chck `SB.checks_join` qr.chck)))
    (decreases n)
  =
  let pios = contract_ios_p #input #output #op #ot #oq ios in
  let tios = contract_ios_t #input #output #op #ot #oq ios in
  let qios = contract_ios_q #input #output #op #ot #oq #st t ios in
  (* Prev states: init at n=0, else the previous step's decomposed state. *)
  let pprev = (if n = 0 then p.init else (step_result_at p pios (n - 1)).s) in
  let tprev = (if n = 0 then t.init else (step_result_at t tios (n - 1)).s) in
  let qprev = (if n = 0 then q.init else (step_result_at q qios (n - 1)).s) in
  (if n > 0 then lemma_step_result_at_system_contract p t q ios (n - 1));
  (* Invert the nested state tuple so the contract's [s_p]/[s_t]/[s_q] reduce to
     the previous sub-run states. *)
  lemma_type_join_fst_tup #sp #(SB.type_join st sq) pprev
    (SB.type_join_tup #st #sq tprev qprev);
  lemma_type_join_snd_tup #sp #(SB.type_join st sq) pprev
    (SB.type_join_tup #st #sq tprev qprev);
  lemma_type_join_fst_tup #st #sq tprev qprev;
  lemma_type_join_snd_tup #st #sq tprev qprev;
  let cr = step_result_at (system_contract p t q) ios n in
  let pr = step_result_at p pios n in
  let tr = step_result_at t tios n in
  let qr = step_result_at q qios n in
  (* [t]'s output at [n] is [tr.v], so [q] is fed [(input, tr.v)] — exactly the
     first component of [qios n]. *)
  assert (stream_of_output t tios n == tr.v);
  assert (cr.v == tr.v);
  assert (cr.s == SB.type_join_tup #sp #(SB.type_join st sq) pr.s
                    (SB.type_join_tup #st #sq tr.s qr.s));
  assert (cr.chck == (SB.checks_assumption pr.v `SB.checks_join`
                      SB.checks_obligation qr.v `SB.checks_join`
                      pr.chck `SB.checks_join` tr.chck `SB.checks_join` qr.chck))
#pop-options

(* Observable [system_contract] unfold: output is [t]'s; assumptions are [p]'s
   value together with all three subsystems' assumptions; obligations are [q]'s
   value together with all three subsystems' obligations. *)
#push-options "--split_queries always --z3rlimit 80"
let lemma_system_contract
  (#input #output: Type)
  (#op #ot #oq #sp #st #sq: option Type)
  (p: SB.system input op sp prop)
  (t: SB.system input ot st output)
  (q: SB.system (input & output) oq sq prop)
  (ios: io_stream input (SB.type_join op (SB.type_join ot oq)))
  (n: nat)
  : Lemma
    (ensures (
      let pios = contract_ios_p #input #output #op #ot #oq ios in
      let tios = contract_ios_t #input #output #op #ot #oq ios in
      let qios = contract_ios_q #input #output #op #ot #oq #st t ios in
      stream_of_output (system_contract p t q) ios n == stream_of_output t tios n /\
      (stream_of_assumptions (system_contract p t q) ios n <==>
        (stream_of_output p pios n /\
         stream_of_assumptions p pios n /\
         stream_of_assumptions t tios n /\
         stream_of_assumptions q qios n)) /\
      (stream_of_obligations (system_contract p t q) ios n <==>
        (stream_of_output q qios n /\
         stream_of_obligations p pios n /\
         stream_of_obligations t tios n /\
         stream_of_obligations q qios n))))
  =
  let pios = contract_ios_p #input #output #op #ot #oq ios in
  let tios = contract_ios_t #input #output #op #ot #oq ios in
  let qios = contract_ios_q #input #output #op #ot #oq #st t ios in
  lemma_step_result_at_system_contract p t q ios n;
  let cr = step_result_at (system_contract p t q) ios n in
  let pr = step_result_at p pios n in
  let tr = step_result_at t tios n in
  let qr = step_result_at q qios n in
  (* Expose the joined checks so [option_prop_sem]/[prop_join] chain the
     assumption/obligation conjunctions. *)
  assert (cr.chck == (SB.checks_assumption pr.v `SB.checks_join`
                      SB.checks_obligation qr.v `SB.checks_join`
                      pr.chck `SB.checks_join` tr.chck `SB.checks_join` qr.chck))
#pop-options
