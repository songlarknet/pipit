(* PROTOTYPE: the core rules restated directly on RAW systems.

   Head-to-head ergonomic comparison against the [sys]-package versions in
   [Pipit.Extensional.Logic] / [System.Logic]. Each rule takes a raw
   [SB.system input oracle state output] with *explicit* oracle/state indices
   instead of the oracle/state-hiding [sys] package, confirming there is no
   barrier: every rule is provable, and the [sys] wrapper [sys_of] is a free
   coercion. Note the equivalence rule needs no propositional [oracle == oracle]
   side-condition — on raw systems the oracle is a shared type parameter, so the
   coercion tax that motivated the [{ t' with oracle = ... }] trick disappears. *)
module Pipit.Extensional.System.Raw

module E   = Pipit.Extensional.Base
module ES  = Pipit.Extensional.Stream
module S   = Pipit.Extensional.System
module SB  = Pipit.System.Base
module SEq = Pipit.Extensional.System.Eq
module SL  = Pipit.Extensional.System.Logic
module L   = Pipit.Extensional.Logic
module Classical = FStar.Classical

(* The free [sys] wrapper: hiding oracle/state is a zero-cost record pack. *)
let sys_of
  (#input #output: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state output)
  : S.sys input output
  = { oracle = oracle; state = state; raw = t }

(* The io-stream a system consumes, built directly (this is exactly what
   [S.with_oracle (sys_of t) is orc] computes). *)
unfold
let io_of
  (#input: Type) (#oracle: option Type)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem oracle))
  : S.io_stream input oracle
  = fun n -> (is n, orc n)

(*** Rule 1: the triple, on a raw system ***)

(* Compare with [L.triple : (stream->stream prop) -> S.sys -> ... -> prop].
   Here [t] is the raw system; the io-stream is inlined. *)
let triple_raw
  (#input #output: Type)
  (#oracle #state: option Type)
  (p: E.stream input -> E.stream prop)
  (t: SB.system input oracle state output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : prop
  =
  forall (is: E.stream input)
         (orc: E.stream (SB.option_type_sem oracle))
         (n: nat).
    let ios = io_of is orc in
    let os  = S.stream_of_output t ios in
    ES.sofar (p is) n ==>
    ES.sofar (S.stream_of_assumptions t ios) n ==>
    (ES.sofar (q is os) n /\ ES.sofar (S.stream_of_obligations t ios) n)

(* The raw triple and the [sys] triple coincide (for a causal postcondition —
   the same side-condition the [sys] rules carry). The io-streams [io_of is orc]
   and [S.with_oracle (sys_of t) is orc] agree pointwise, so every system stream
   is congruent and [q] transports by causality. *)
#push-options "--split_queries always --z3rlimit 100"
let lemma_triple_bridge
  (#input #output: Type)
  (#oracle #state: option Type)
  (p: E.stream input -> E.stream prop)
  (t: SB.system input oracle state output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires ES.causal2 q)
    (ensures triple_raw p t q <==> L.triple p (sys_of t) q)
  =
  let ts = sys_of t in
  introduce forall (is: E.stream input)
                   (orc: E.stream (SB.option_type_sem oracle))
                   (n: nat).
      ((let ios = io_of is orc in
        let os  = S.stream_of_output t ios in
        (ES.sofar (p is) n ==> ES.sofar (S.stream_of_assumptions t ios) n ==>
         (ES.sofar (q is os) n /\ ES.sofar (S.stream_of_obligations t ios) n)))
       <==>
       (let ios' = S.with_oracle ts is orc in
        let os'  = S.stream_of_output ts.raw ios' in
        (ES.sofar (p is) n ==> ES.sofar (S.stream_of_assumptions ts.raw ios') n ==>
         (ES.sofar (q is os') n /\ ES.sofar (S.stream_of_obligations ts.raw ios') n))))
  with begin
    let ios  = io_of is orc in
    let ios' = S.with_oracle ts is orc in
    assert (forall (k: nat). ios k == ios' k);
    introduce forall (k: nat). S.stream_of_output t ios k == S.stream_of_output t ios' k
      with S.lemma_stream_of_output_congruence t ios ios' k;
    introduce forall (k: nat). S.stream_of_assumptions t ios k == S.stream_of_assumptions t ios' k
      with S.lemma_stream_of_assumptions_congruence t ios ios' k;
    introduce forall (k: nat). S.stream_of_obligations t ios k == S.stream_of_obligations t ios' k
      with S.lemma_stream_of_obligations_congruence t ios ios' k;
    ES.lemma_causal2_prefix q is is
      (S.stream_of_output t ios) (S.stream_of_output t ios') n
  end
#pop-options

(*** Rule 2: 1-induction (k-induction, k=1), on a raw system ***)

(* Premises [L.base_case]/[L.step_case] already take a *raw* system, so no
   wrapping is needed there; only the conclusion is bridged. *)
let induct1_raw
  (#input #output: Type)
  (#oracle #state: option Type)
  (t: SB.system input oracle state output)
  (pp: input -> nat -> prop)
  (qq: input -> output -> nat -> prop)
  : Lemma
    (requires L.base_case t pp qq /\ L.step_case t pp qq)
    (ensures triple_raw (L.pw_pre pp) t (L.pw_post qq))
  =
  L.induct1_pw (sys_of t) pp qq;
  assert (ES.causal2 (L.pw_post qq));
  lemma_triple_bridge (L.pw_pre pp) t (L.pw_post qq)

(*** Rule 3: observational equivalence + transport, on raw systems ***)

(* [equiv_raw]: shared oracle *type parameter*, possibly different states. No
   [t2.oracle == t1.oracle] refinement — that is automatic here. *)
let equiv_raw
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (t1: SB.system input oracle st1 output)
  (t2: SB.system input oracle st2 output)
  : prop
  =
  forall (is: E.stream input)
         (orc: E.stream (SB.option_type_sem oracle))
         (n: nat).
    let ios = io_of is orc in
    S.stream_of_output t1 ios n == S.stream_of_output t2 ios n /\
    (S.stream_of_assumptions t1 ios n <==> S.stream_of_assumptions t2 ios n) /\
    (S.stream_of_obligations t1 ios n <==> S.stream_of_obligations t2 ios n)

(* [equiv_raw] coincides with the [sys]-level [SEq.equiv] on the wrapped
   systems. The wrapped oracles are definitionally equal, so no coercion. *)
#push-options "--split_queries always --z3rlimit 100"
let lemma_equiv_bridge
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (t1: SB.system input oracle st1 output)
  (t2: SB.system input oracle st2 output)
  : Lemma (equiv_raw t1 t2 <==> SEq.equiv (sys_of t1) (sys_of t2))
  =
  let s1 = sys_of t1 in
  let s2 = sys_of t2 in
  introduce forall (is: E.stream input)
                   (orc: E.stream (SB.option_type_sem oracle))
                   (n: nat).
      ((let ios = io_of is orc in
        S.stream_of_output t1 ios n == S.stream_of_output t2 ios n /\
        (S.stream_of_assumptions t1 ios n <==> S.stream_of_assumptions t2 ios n) /\
        (S.stream_of_obligations t1 ios n <==> S.stream_of_obligations t2 ios n))
       <==>
       (let ios1 = S.with_oracle s1 is orc in
        let ios2 = S.with_oracle s2 is orc in
        S.stream_of_output s1.raw ios1 n == S.stream_of_output s2.raw ios2 n /\
        (S.stream_of_assumptions s1.raw ios1 n <==> S.stream_of_assumptions s2.raw ios2 n) /\
        (S.stream_of_obligations s1.raw ios1 n <==> S.stream_of_obligations s2.raw ios2 n)))
  with begin
    let ios  = io_of is orc in
    let ios1 = S.with_oracle s1 is orc in
    let ios2 = S.with_oracle s2 is orc in
    assert (forall (k: nat). ios k == ios1 k /\ ios k == ios2 k);
    S.lemma_stream_of_output_congruence      t1 ios ios1 n;
    S.lemma_stream_of_assumptions_congruence t1 ios ios1 n;
    S.lemma_stream_of_obligations_congruence t1 ios ios1 n;
    S.lemma_stream_of_output_congruence      t2 ios ios2 n;
    S.lemma_stream_of_assumptions_congruence t2 ios ios2 n;
    S.lemma_stream_of_obligations_congruence t2 ios ios2 n
  end
#pop-options

(* Transport a raw triple along a raw equivalence. Delegates to the [sys]-level
   [equiv_transport]; the oracle side-condition [(sys_of t2).oracle ==
   (sys_of t1).oracle] holds definitionally (both are [oracle]). *)
let equiv_transport_raw
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (p: E.stream input -> E.stream prop)
  (t1: SB.system input oracle st1 output)
  (t2: SB.system input oracle st2 output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires ES.causal2 q /\ triple_raw p t2 q /\ equiv_raw t1 t2)
    (ensures triple_raw p t1 q)
  =
  lemma_triple_bridge p t2 q;
  lemma_equiv_bridge t1 t2;
  SL.equiv_transport p (sys_of t1) (sys_of t2) q;
  lemma_triple_bridge p t1 q
