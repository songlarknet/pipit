(* PROTOTYPE: equivalence as a check-surfacing contract.

   Confirms the design claim: observational equivalence can be phrased as a
   plain contract [ { const True } pair_diag t t' { eqQ } ] provided the pairing
   combinator *surfaces each side's checks as observable output*. The key lemma
   [lemma_eqQ_agree] shows the postcondition [eqQ] on the paired output is
   exactly the three-way agreement (output / assumptions / obligations) that
   [System.Eq.equiv_elim] provides — so the stream-based [equiv] is reproduced
   by a system-centric contract, with no stream abstraction in sight. *)
module Pipit.Extensional.System.Pair

module E   = Pipit.Extensional.Base
module ES  = Pipit.Extensional.Stream
module S   = Pipit.Extensional.System
module SB  = Pipit.System.Base
module SEq = Pipit.Extensional.System.Eq
module SL  = Pipit.Extensional.System.Logic
module L   = Pipit.Extensional.Logic
module Classical = FStar.Classical

(* Each side emits (its output, its step-assumption prop, its step-obligation
   prop). This is what lets a single output-only postcondition observe checks. *)
let obs_out  (output: Type) = output & prop & prop
let pair_out (output: Type) = obs_out output & obs_out output

(* Raw diagonal pairing: run [t] and [t'] in lock-step on the *same* input and
   the *same* oracle (shared oracle type param [oracle]), surfacing each side's
   output and checks as the observable output. The pair's own checks are none. *)
let system_pair_diag
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (t:  SB.system input oracle st1 output)
  (t': SB.system input oracle st2 output)
  : SB.system input oracle (SB.type_join st1 st2) (pair_out output)
  =
  {
    init = SB.type_join_tup #st1 #st2 t.init t'.init;
    step = (fun i o s ->
      let s1 = SB.type_join_fst #st1 #st2 s in
      let s2 = SB.type_join_snd #st1 #st2 s in
      let r  = t.step  i o s1 in
      let r' = t'.step i o s2 in
      {
        s = SB.type_join_tup #st1 #st2 r.s r'.s;
        v = ((r.v,  SB.option_prop_sem r.chck.assumptions,  SB.option_prop_sem r.chck.obligations),
             (r'.v, SB.option_prop_sem r'.chck.assumptions, SB.option_prop_sem r'.chck.obligations));
        chck = SB.checks_none;
      });
  }

(* Alignment: the pair's step result exposes both sides' step results. *)
#push-options "--split_queries always --z3rlimit 60"
let rec lemma_step_result_at_pair_diag
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (t:  SB.system input oracle st1 output)
  (t': SB.system input oracle st2 output)
  (ios: S.io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures (
      let pr = S.step_result_at (system_pair_diag t t') ios n in
      let r  = S.step_result_at t  ios n in
      let r' = S.step_result_at t' ios n in
      pr.v == ((r.v,  SB.option_prop_sem r.chck.assumptions,  SB.option_prop_sem r.chck.obligations),
               (r'.v, SB.option_prop_sem r'.chck.assumptions, SB.option_prop_sem r'.chck.obligations)) /\
      pr.s == SB.type_join_tup #st1 #st2 r.s r'.s /\
      pr.chck == SB.checks_none))
    (decreases n)
  =
  let prev1 = (if n = 0 then t.init  else (S.step_result_at t  ios (n - 1)).s) in
  let prev2 = (if n = 0 then t'.init else (S.step_result_at t' ios (n - 1)).s) in
  (if n > 0 then lemma_step_result_at_pair_diag t t' ios (n - 1));
  S.lemma_type_join_fst_tup #st1 #st2 prev1 prev2;
  S.lemma_type_join_snd_tup #st1 #st2 prev1 prev2
#pop-options

(* Observable-output unfold + the pair's checks are trivial. *)
let lemma_pair_diag
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (t:  SB.system input oracle st1 output)
  (t': SB.system input oracle st2 output)
  (ios: S.io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures (
      S.stream_of_output (system_pair_diag t t') ios n ==
        ((S.stream_of_output t ios n, S.stream_of_assumptions t ios n, S.stream_of_obligations t ios n),
         (S.stream_of_output t' ios n, S.stream_of_assumptions t' ios n, S.stream_of_obligations t' ios n)) /\
      S.stream_of_assumptions (system_pair_diag t t') ios n == True /\
      S.stream_of_obligations (system_pair_diag t t') ios n == True))
  =
  lemma_step_result_at_pair_diag t t' ios n

(* The equality postcondition on paired output: outputs equal, assumptions and
   obligations logically equivalent. *)
let eqQ (#output: Type) (p: pair_out output) : prop =
  let ((o1, a1, g1), (o2, a2, g2)) = p in
  o1 == o2 /\ (a1 <==> a2) /\ (g1 <==> g2)

(* KEY: [eqQ] on the surfaced paired output is exactly [equiv_elim]'s three-way
   agreement between [t] and [t'] at step [n]. *)
let lemma_eqQ_agree
  (#input #output: Type)
  (#oracle #st1 #st2: option Type)
  (t:  SB.system input oracle st1 output)
  (t': SB.system input oracle st2 output)
  (ios: S.io_stream input oracle)
  (n: nat)
  : Lemma
    (ensures (
      eqQ (S.stream_of_output (system_pair_diag t t') ios n) <==>
        (S.stream_of_output t ios n == S.stream_of_output t' ios n /\
         (S.stream_of_assumptions t ios n <==> S.stream_of_assumptions t' ios n) /\
         (S.stream_of_obligations t ios n <==> S.stream_of_obligations t' ios n))))
  =
  lemma_pair_diag t t' ios n

(*** Equivalence as a contract: [ { const True } pair_diag t t' { eqQ } ] ***)

(* The diagonal pairing as a [sys] package. The record update aligns [t']'s
   (propositionally equal) oracle with [t]'s so both raw systems share the oracle
   type parameter [t.oracle] — the same trick as [lemma_equiv_contract_t]. *)
let pair_diag_sys
  (#input #output: Type)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  : S.sys input (pair_out output)
  =
  let t'' : S.sys input output = { t' with oracle = t.oracle } in
  {
    oracle = t.oracle;
    state  = SB.type_join t.state t''.state;
    raw    = system_pair_diag t.raw t''.raw;
  }

(* Equivalence *as a triple*: the paired system, run from any input/oracle,
   emits equal outputs and matching checks at every step. Because [pair_diag]
   surfaces checks as output, this single output-only postcondition [eqQ]
   captures full behavioural equivalence — no rely/guarantee internalisation, no
   stream abstraction. This is literally [ { const True } pair_diag t t' { eqQ } ]. *)
let equiv_c
  (#input #output: Type)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  : prop
  =
  L.triple
    (L.pw_pre (fun (_: input) (_: nat) -> True))
    (pair_diag_sys t t')
    (L.pw_post (fun (_: input) (o: pair_out output) (_: nat) -> eqQ o))

(* Pointwise correspondence: at every step, the paired system's checks are
   trivial and [eqQ] on its output is exactly the three-way agreement between
   [t] and [t'] that [equiv]/[equiv_elim] use. *)
#push-options "--split_queries always --z3rlimit 100"
let lemma_pair_corresp
  (#input #output: Type)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem (pair_diag_sys t t').oracle))
  (n: nat)
  : Lemma
    (ensures (
      let tt     = pair_diag_sys t t' in
      let ios    = S.with_oracle tt is orc in
      let ios_t  = S.with_oracle t  is orc in
      let ios_t' = S.with_oracle t' is orc in
      S.stream_of_assumptions tt.raw ios n == True /\
      S.stream_of_obligations tt.raw ios n == True /\
      (eqQ (S.stream_of_output tt.raw ios n) <==>
        (S.stream_of_output t.raw ios_t n == S.stream_of_output t'.raw ios_t' n /\
         (S.stream_of_assumptions t.raw ios_t n <==> S.stream_of_assumptions t'.raw ios_t' n) /\
         (S.stream_of_obligations t.raw ios_t n <==> S.stream_of_obligations t'.raw ios_t' n)))))
  =
  let tt  = pair_diag_sys t t' in
  let t'' : S.sys input output = { t' with oracle = t.oracle } in
  assert (t'' == t');
  let ios    = S.with_oracle tt  is orc in
  let ios_t  = S.with_oracle t   is orc in
  let ios_t''= S.with_oracle t'' is orc in
  (* [with_oracle] ignores the system: all these io-streams are [fun m -> (is m, orc m)]. *)
  assert (forall (m: nat). ios m == ios_t m /\ ios m == ios_t'' m);
  (* [tt.raw == system_pair_diag t.raw t''.raw]; surface checks + eqQ agreement. *)
  lemma_pair_diag t.raw t''.raw ios n;
  lemma_eqQ_agree t.raw t''.raw ios n;
  (* Move [t]'s and [t'']'s observations from [ios] to their own [with_oracle]. *)
  S.lemma_stream_of_output_congruence      t.raw   ios ios_t   n;
  S.lemma_stream_of_assumptions_congruence t.raw   ios ios_t   n;
  S.lemma_stream_of_obligations_congruence t.raw   ios ios_t   n;
  S.lemma_stream_of_output_congruence      t''.raw ios ios_t'' n;
  S.lemma_stream_of_assumptions_congruence t''.raw ios ios_t'' n;
  S.lemma_stream_of_obligations_congruence t''.raw ios ios_t'' n
#pop-options

(* THE PAYOFF: equivalence-as-a-contract reproduces the stream-based [equiv]
   exactly. So the check-surfacing contract *is* [equiv_elim], with no stream
   machinery — confirming streams are inessential for equational reasoning. *)
#push-options "--split_queries always --z3rlimit 200 --fuel 2 --ifuel 1"
let lemma_equiv_c_iff
  (#input #output: Type)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  : Lemma (equiv_c t t' <==> SEq.equiv t t')
  =
  let tt = pair_diag_sys t t' in
  Classical.forall_intro_3 (lemma_pair_corresp t t');
  (* Forward: from the contract triple, read off the agreement at each step. *)
  introduce equiv_c t t' ==> SEq.equiv t t'
  with _. begin
    introduce forall (is: E.stream input)
                     (orc: E.stream (SB.option_type_sem t.oracle))
                     (n: nat).
        (let ios_t  = S.with_oracle t  is orc in
         let ios_t' = S.with_oracle t' is orc in
         S.stream_of_output t.raw ios_t n == S.stream_of_output t'.raw ios_t' n /\
         (S.stream_of_assumptions t.raw ios_t n <==> S.stream_of_assumptions t'.raw ios_t' n) /\
         (S.stream_of_obligations t.raw ios_t n <==> S.stream_of_obligations t'.raw ios_t' n))
    with begin
      let ios = S.with_oracle tt is orc in
      ES.sofar_index (L.pw_post (fun (_: input) (o: pair_out output) (_: nat) -> eqQ o)
                        is (S.stream_of_output tt.raw ios)) n
    end
  end;
  (* Backward: the agreement at each step discharges the contract triple. *)
  introduce SEq.equiv t t' ==> equiv_c t t'
  with _. begin
    introduce forall (is: E.stream input)
                     (orc: E.stream (SB.option_type_sem tt.oracle))
                     (n: nat).
        (let ios = S.with_oracle tt is orc in
         ES.sofar (L.pw_pre (fun (_: input) (_: nat) -> True) is) n ==>
         ES.sofar (S.stream_of_assumptions tt.raw ios) n ==>
         (ES.sofar (L.pw_post (fun (_: input) (o: pair_out output) (_: nat) -> eqQ o)
                      is (S.stream_of_output tt.raw ios)) n /\
          ES.sofar (S.stream_of_obligations tt.raw ios) n))
    with introduce _ ==> _ with _. introduce _ ==> _ with _. begin
      let ios = S.with_oracle tt is orc in
      introduce forall (k: nat). k <= n ==>
          eqQ (S.stream_of_output tt.raw ios k)
      with introduce _ ==> _ with _.
        SEq.equiv_elim t t' is orc k
    end
  end
