(* Worked example: prove  { True } (µx. 0 fby x) { x. x = 0 }.

   The induction is provided entirely by [Logic.mu]; [Logic.fby] contributes
   only the output shift, and the recursive variable [x] is read by the
   projection [System.map fst System.id]. *)
module Pipit.Extensional.Example

module E  = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module S  = Pipit.Extensional.System
module L  = Pipit.Extensional.Logic
module SL = Pipit.Extensional.System.Logic
module SEq = Pipit.Extensional.System.Eq
module SB = Pipit.System.Base
module PT = Pipit.Tactics
(* The program  µx. 0 fby x  (unit input, int output). *)
let t_x   : S.sys (int & unit) int = S.map fst S.id
let body  : S.sys (int & unit) int = S.fby 0 t_x
let prog  : S.sys unit int         = S.mu body

(* Precondition [True]; postcondition [x = 0]. *)
let p_true : E.stream unit -> E.stream prop = fun _ -> (fun _ -> True)
let q_zero : E.stream unit -> E.stream int -> E.stream prop = fun _ os -> (fun n -> os n == 0)

let p_pre  = L.mu_body_pre p_true q_zero
let q_post = L.mu_body_post q_zero

(* Body triple for the projection [t_x = map fst id], with [q_post] post-composed
   with the [fby 0] shift. Built compositionally by [Logic.map] then the [id] leaf
   rule; the leftover [id] premise is the pure stream fact
   [sofar (p_pre is) n ==> sofar (q_post is (0 fby fst is)) n]. *)
#push-options "--z3rlimit 50"
let lemma_t_x_triple (_: unit)
  : Lemma (L.triple p_pre t_x (fun is ot -> q_post is (ES.fby 0 ot)))
  =
  let qid : E.stream (int & unit) -> E.stream (int & unit) -> E.stream prop =
    fun is ot -> q_post is (ES.fby 0 (ES.map fst ot)) in
  assert (ES.causal2 (fun (is: E.stream (int & unit)) (ot: E.stream int) ->
                        q_post is (ES.fby 0 ot)));
  assert (ES.causal2 qid);
  introduce forall (is: E.stream (int & unit)) (n: nat).
      ES.sofar (p_pre is) n ==> ES.sofar (qid is is) n
    with introduce _ ==> _ with _.
      ES.sofar_index (p_pre is) n;
  L.id p_pre qid;
  L.map fst (S.id #(int & unit)) p_pre (fun is ot -> q_post is (ES.fby 0 ot))
#pop-options

(* The final proof: [fby] shifts the body, [mu] closes the recursion. *)
let lemma_zero_rec (_: unit)
  : Lemma (L.triple p_true prog q_zero)
  =
  assert (ES.causal p_true);
  assert (ES.causal2 q_zero);
  assert (ES.causal2 q_post);
  lemma_t_x_triple ();
  L.fby 0 t_x p_pre q_post;
  L.mu p_true body q_zero

(* The oracle-free program  µfby x. 0 fby x  (= constant 0), closed by the
   [mufby] combinator so it carries no oracle and can appear in specifications;
   used by the induction examples below. *)
let prog_mufby : S.sys unit int = S.mufby 0 t_x

(*** Example 1, via transition induction:  { True } mufby 0 t_x { x = 0 } ***)

(* Same result again, discharged by transition-system 1-induction. [induct1_pw]
   reduces the triple to a base case and a step case over [t.step] with the state
   abstracted (no [step_result_at] recursion). Both are normalised with
   [norm_full]: since [prog_mufby] is a concrete system, unfolding it fully
   reduces [option_type_sem] / [type_join] (the register), leaving a trivial
   arithmetic goal for SMT. *)
let lemma_zero_rec_induct (_: unit)
  : Lemma (L.triple p_true prog_mufby q_zero)
  =
  let pp : unit -> nat -> prop = fun _ _ -> True in
  let qq : unit -> int -> nat -> prop = fun _ o _ -> o == 0 in
  assert (L.base_case prog_mufby.raw pp qq) by (PT.norm_full []);
  assert (L.step_case prog_mufby.raw pp qq) by (PT.norm_full []);
  L.induct1_pw prog_mufby pp qq

(*** Example 1, system-valued spec:  { const True } mufby 0 t_x { map (= 0) } ***)

(* The same specification with pre/postconditions written as (prop-valued)
   systems: [const True] and "the output equals 0". Because these are systems,
   their decoded stream predicates are causal by construction, so
   [System.Logic.triple] carries no causality side-condition. *)
let sl_pre  : S.sys unit prop = S.const True
let sl_post : S.sys (unit & int) prop = S.map (fun (io: unit & int) -> snd io == 0) S.id

(* Discharged by product-system 1-induction: the base and step cases run over the
   three step functions ([sl_pre] | [prog_mufby] | [sl_post]) with the state
   abstracted; [norm_full] reduces the concrete systems and SMT closes both —
   with no causality side-condition and no stream reasoning at all. *)
let lemma_zero_rec_sys_induct (_: unit)
  : Lemma (SL.triple sl_pre prog_mufby sl_post)
  =
  assert (SL.base_case_sys sl_pre prog_mufby sl_post) by (PT.norm_full []);
  assert (SL.step_case_sys sl_pre prog_mufby sl_post) by (PT.norm_full []);
  SL.induct1_sys sl_pre prog_mufby sl_post

(*** Example 3: two counters sharing a subcomputation (applicative invariant) ***)

(* A saturation-free counter  µx. (0 fby x) + 1  built with [mufby]; its output
   is the step index plus one (1, 2, 3, ...). *)
let incr    : S.sys (int & unit) int = S.map (fun (p: int & unit) -> fst p + 1) S.id
let counter : S.sys unit int         = S.mufby 0 incr

(* Named pair constructor so the [ap]/[map] CSE law's [fun x -> mkpair x x]
   matches [both_cse] syntactically (avoids alpha/beta lambda non-unification). *)
let mkpair (a b: int) : int & int = (a, b)

(* [both] runs two independent copies of [counter] in lock-step via the
   applicative [ap], pairing their outputs. Crucially [ap] joins the two counter
   states, so the product carries *two* separate registers: the analysis cannot
   see a priori that the two components agree. *)
let both : S.sys unit (int & int) =
  S.ap (S.map mkpair counter) counter

let both_pre : S.sys unit prop = S.const True

(* Lightweight non-constant example: the counter is always positive. Exercises
   [mufby] + [induct1_sys] on a *counting* program (output [1], then register+1),
   discharged by [norm_full] with no auxiliary invariant. *)
let counter_pos : S.sys (unit & int) prop = S.map (fun (io: unit & int) -> b2t (snd io >= 1)) S.id

let lemma_counter_pos (_: unit)
  : Lemma (SL.triple both_pre counter counter_pos)
  =
  assert (SL.base_case_sys both_pre counter counter_pos) by (PT.norm_full []);
  assert (SL.step_case_sys both_pre counter counter_pos) by (PT.norm_full []);
  SL.induct1_sys both_pre counter counter_pos

(* The applicative invariant: the two counter copies always agree. This is the
   relational fact an AIL-style analysis would synthesise ([c1 = c2]). *)
let g_eq (io: unit & (int & int)) : prop = fst (snd io) == snd (snd io)
unfold let post_eq : S.sys (unit & (int & int)) prop = S.map g_eq S.id

(* Part 1 (automatic): 1-induction over the product system discovers the
   invariant [c1 = c2]. The base/step cases reduce (via [norm_full]) to trivial
   arithmetic because both registers step identically. *)
let lemma_both_agree (_: unit)
  : Lemma (SL.triple both_pre both post_eq)
  =
  assert (SL.base_case_sys both_pre both post_eq) by (PT.norm_full []);
  assert (SL.step_case_sys both_pre both post_eq) by (PT.norm_full []);
  SL.induct1_sys both_pre both post_eq

(* The target safety property: a bound established on the first counter transfers
   to the second. This is NOT inductive on its own — the step case needs
   [c1_{n-1} < K] to conclude [c2_n <= K], but knowing only [c2_{n-1} <= K] (the
   property at [n-1]) is too weak, since the two registers are independent. It
   goes through only once we know the applicative invariant [c1 = c2]. *)
let kbound : int = 100
let g_bound (io: unit & (int & int)) : prop =
  fst (snd io) <= kbound ==> snd (snd io) <= kbound
unfold let post_bound : S.sys (unit & (int & int)) prop = S.map g_bound S.id

(* Part 2 (manual): weaken the invariant [c1 = c2] to the target property by the
   rule of consequence. TODO (follow-up): re-express against the new contract-
   validity [triple]. It needs an SL-level postcondition-consequence rule
   (weaken [post]'s value inside [contract pre t post]); the old proof used the
   [Logic]-level [consequence] on the value-only triple, which no longer matches
   [SL.triple]. Deferred with [equiv_transport_sys]. *)
// #push-options "--z3rlimit 40"
// let lemma_both_bound (_: unit)
//   : Lemma (SL.triple both_pre both post_bound)
//   =
//   introduce forall (is: E.stream unit) (os: E.stream (int & int)) (n: nat).
//       SL.spred2 post_eq is os n ==> SL.spred2 post_bound is os n
//   with begin
//     SL.lemma_spred2_map_id g_eq is os n;
//     SL.lemma_spred2_map_id g_bound is os n
//   end;
//   lemma_both_agree ();
//   L.consequence both
//     (SL.spred both_pre) (SL.spred both_pre)
//     (SL.spred2 post_bound) (SL.spred2 post_eq)
// #pop-options

(*** Example 3', same property via a semantic CSE rewrite (equiv + transport) ***)

(* The CSE'd program: one counter, output duplicated. [ap]'s two registers are
   collapsed to one -- and [ap_map_cse] proves this is observationally the same. *)
let both_cse : S.sys unit (int & int) = S.map (fun (x: int) -> mkpair x x) counter

(* The headline rewrite, admit-free: the two-register [both] is [equiv] to the
   single-register [both_cse]. This is one instance of the reusable applicative
   CSE law. *)
let lemma_both_cse (_: unit)
  : Lemma (SEq.equiv both both_cse)
  =
  SEq.lemma_ap_map_cse mkpair counter

(* On the shared form the target property is trivially inductive: both outputs
   are the *same* counter value, so [c <= K ==> c <= K] holds by construction.
   [induct1_sys] discharges it via [norm_full] with no auxiliary invariant. *)
let lemma_both_cse_triple (_: unit)
  : Lemma (SL.triple both_pre both_cse post_bound)
  =
  assert (SL.base_case_sys both_pre both_cse post_bound) by (PT.norm_full []);
  assert (SL.step_case_sys both_pre both_cse post_bound) by (PT.norm_full []);
  SL.induct1_sys both_pre both_cse post_bound

(* The contract systems for [both] and [both_cse] are observationally equivalent:
   both are concrete and oracle-free (oracles reduce to [None]), [both] and
   [both_cse] agree observationally by the CSE law, and [both_pre]/[post_bound]
   are shared — so the whole contract streams coincide. *)
#push-options "--split_queries always --z3rlimit 300 --fuel 2 --ifuel 1"
let lemma_both_contract_equiv (_: unit)
  : Lemma (SEq.equiv (S.contract both_pre both post_bound) (S.contract both_pre both_cse post_bound))
  =
  lemma_both_cse ();
  let c  = S.contract both_pre both     post_bound in
  let c' = S.contract both_pre both_cse post_bound in
  let aux (is: E.stream unit) (orc: E.stream (SB.option_type_sem c.oracle)) (n: nat)
    : Lemma (
        let ios  = S.with_oracle c  is orc in
        let ios' = S.with_oracle c' is orc in
        S.stream_of_output c.raw ios n == S.stream_of_output c'.raw ios' n /\
        (S.stream_of_assumptions c.raw ios n <==> S.stream_of_assumptions c'.raw ios' n) /\
        (S.stream_of_obligations c.raw ios n <==> S.stream_of_obligations c'.raw ios' n))
    =
    let ios  = S.with_oracle c  is orc in
    let ios' = S.with_oracle c' is orc in
    lemma_both_cse ();
    S.lemma_system_contract both_pre.raw both.raw     post_bound.raw ios  n;
    S.lemma_system_contract both_pre.raw both_cse.raw post_bound.raw ios' n;
    let tios  = S.contract_ios_t #unit #(int & int) #both_pre.oracle #both.oracle     #post_bound.oracle ios  in
    let tios' = S.contract_ios_t #unit #(int & int) #both_pre.oracle #both_cse.oracle #post_bound.oracle ios' in
    let pios  = S.contract_ios_p #unit #(int & int) #both_pre.oracle #both.oracle     #post_bound.oracle ios  in
    let pios' = S.contract_ios_p #unit #(int & int) #both_pre.oracle #both_cse.oracle #post_bound.oracle ios' in
    let qios  = S.contract_ios_q #unit #(int & int) #both_pre.oracle #both.oracle     #post_bound.oracle #both.state     both.raw     ios  in
    let qios' = S.contract_ios_q #unit #(int & int) #both_pre.oracle #both_cse.oracle #post_bound.oracle #both_cse.state both_cse.raw ios' in
    let u : E.stream unit = fun (_: nat) -> () in
    let uio   = S.with_oracle both     is u in
    let uio'  = S.with_oracle both_cse is u in
    (* Concrete oracles reduce to [None], so the [t]-projections are the unit
       io-streams; [equiv both both_cse] then equates their outputs. *)
    assert (forall (k: nat). tios k == uio k);
    assert (forall (k: nat). tios' k == uio' k);
    introduce forall (k: nat).
        S.stream_of_output both.raw uio k == S.stream_of_output both_cse.raw uio' k /\
        (S.stream_of_assumptions both.raw uio k <==> S.stream_of_assumptions both_cse.raw uio' k) /\
        (S.stream_of_obligations both.raw uio k <==> S.stream_of_obligations both_cse.raw uio' k)
      with SEq.equiv_elim both both_cse is u k;
    (* [both]/[both_cse] agree on the [t]-projection (all three streams). *)
    introduce forall (k: nat).
        (S.stream_of_output      both.raw tios k == S.stream_of_output      both_cse.raw tios' k) /\
        (S.stream_of_assumptions both.raw tios k <==> S.stream_of_assumptions both_cse.raw tios' k) /\
        (S.stream_of_obligations both.raw tios k <==> S.stream_of_obligations both_cse.raw tios' k)
      with begin
        S.lemma_stream_of_output_congruence      both.raw     tios  uio  k;
        S.lemma_stream_of_output_congruence      both_cse.raw tios' uio' k;
        S.lemma_stream_of_assumptions_congruence both.raw     tios  uio  k;
        S.lemma_stream_of_assumptions_congruence both_cse.raw tios' uio' k;
        S.lemma_stream_of_obligations_congruence both.raw     tios  uio  k;
        S.lemma_stream_of_obligations_congruence both_cse.raw tios' uio' k
      end;
    (* Equal [t]-outputs mean [post] is fed the same pair; [pre] sees the same
       input. Both projections coincide, so [pre]/[post] streams agree. *)
    assert (forall (k: nat). pios k == pios' k);
    assert (forall (k: nat). qios k == qios' k);
    introduce forall (k: nat).
        (S.stream_of_output      post_bound.raw qios k == S.stream_of_output      post_bound.raw qios' k) /\
        (S.stream_of_assumptions post_bound.raw qios k <==> S.stream_of_assumptions post_bound.raw qios' k) /\
        (S.stream_of_obligations post_bound.raw qios k <==> S.stream_of_obligations post_bound.raw qios' k)
      with begin
        S.lemma_stream_of_output_congruence      post_bound.raw qios qios' k;
        S.lemma_stream_of_assumptions_congruence post_bound.raw qios qios' k;
        S.lemma_stream_of_obligations_congruence post_bound.raw qios qios' k
      end;
    introduce forall (k: nat).
        (S.stream_of_output      both_pre.raw pios k == S.stream_of_output      both_pre.raw pios' k) /\
        (S.stream_of_assumptions both_pre.raw pios k <==> S.stream_of_assumptions both_pre.raw pios' k) /\
        (S.stream_of_obligations both_pre.raw pios k <==> S.stream_of_obligations both_pre.raw pios' k)
      with begin
        S.lemma_stream_of_output_congruence      both_pre.raw pios pios' k;
        S.lemma_stream_of_assumptions_congruence both_pre.raw pios pios' k;
        S.lemma_stream_of_obligations_congruence both_pre.raw pios pios' k
      end
  in
  Classical.forall_intro_3 aux
#pop-options

(* Same goal as [lemma_both_bound], but discharged by the semantic rewrite:
   prove the property on [both_cse] (trivial), then transport it to [both]
   along [equiv]. No induction / no invariant on [both] itself. *)
let lemma_both_bound_cse (_: unit)
  : Lemma (SL.triple both_pre both post_bound)
  =
  lemma_both_cse_triple ();
  lemma_both_contract_equiv ();
  assert (ES.causal2 (L.pw_post (SL.ptrue_post #unit #(int & int))));
  SL.equiv_transport
    (L.pw_pre (SL.ptrue_pre #unit))
    (S.contract both_pre both     post_bound)
    (S.contract both_pre both_cse post_bound)
    (L.pw_post (SL.ptrue_post #unit #(int & int)))





