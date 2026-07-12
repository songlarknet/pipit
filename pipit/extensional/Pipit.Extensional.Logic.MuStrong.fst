(* PROTOTYPE: the STRONG guarded-recursion rule.

   The weak [mu] rule remembers only [pre(sofar(q x))] about the recursive value
   x. The strong rule additionally hands the body the fixpoint equation the knot
   already guarantees --- [sofar(x = body)] --- which [system_mu] emits as its
   per-step assumption [v == stp1.v] and the triple's [sofar]-conditioning
   collects into the full history for free.

   Realisation ("keep the knot's assumption"): wrap the body with [assume_fix],
   which re-adds the per-step assumption [x == body-output]. Then
     - [mu (assume_fix body)] is observationally equivalent to [mu body]
       (the extra assumption merely duplicates the knot's own, which is idempotent);
     - so [mu] on [assume_fix body] + [equiv_transport] back to [mu body]
       gives the strong rule with NO cloning of [mu_aux]. *)
module Pipit.Extensional.Logic.MuStrong

module E   = Pipit.Extensional.Base
module ES  = Pipit.Extensional.Stream
module S   = Pipit.Extensional.System
module SB  = Pipit.System.Base
module SEq = Pipit.Extensional.System.Eq
module SL  = Pipit.Extensional.System.Logic
module L   = Pipit.Extensional.Logic
module Classical = FStar.Classical

(* Wrap a mu-body with the knot's per-step assumption [x == output], where
   [x = fst input] is the recursive feedback and [output] is the body's own
   output at that step. *)
let system_assume_fix
  (#input #output: Type)
  (#oracle #state: option Type)
  (t: SB.system (output & input) oracle state output)
  : SB.system (output & input) oracle state output
  =
  {
    init = t.init;
    step = (fun i o s ->
      let r = t.step i o s in
      { r with chck = SB.checks_join (SB.checks_assumption (fst i == r.v)) r.chck });
  }

let assume_fix
  (#input #output: Type)
  (body: S.sys (output & input) output)
  : S.sys (output & input) output
  = { body with raw = system_assume_fix body.raw }

(* Step-level comparison: [system_mu t] and [system_mu (assume_fix t)] have the
   same state and output at every step; their assumptions are logically
   equivalent (the extra fixpoint assumption duplicates the knot's own), and
   their obligations coincide. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec lemma_step_result_mu_af
  (#input #output: Type)
  (#oracle #state: option Type)
  (t: SB.system (output & input) oracle state output)
  (ios: S.io_stream input (SB.type_join (Some output) oracle))
  (n: nat)
  : Lemma
    (ensures (
      let a = S.step_result_at (SB.system_mu t) ios n in
      let b = S.step_result_at (SB.system_mu (system_assume_fix t)) ios n in
      a.s == b.s /\
      a.v == b.v /\
      (SB.option_prop_sem a.chck.assumptions <==> SB.option_prop_sem b.chck.assumptions) /\
      (SB.option_prop_sem a.chck.obligations <==> SB.option_prop_sem b.chck.obligations)))
    (decreases n)
  =
  if n = 0 then () else lemma_step_result_mu_af t ios (n - 1)
#pop-options

(* [mu body] and [mu (assume_fix body)] are observationally equivalent. *)
#push-options "--split_queries always --z3rlimit 100"
let lemma_equiv_mu_assume_fix
  (#input #output: Type)
  (body: S.sys (output & input) output)
  : Lemma (SEq.equiv (S.mu body) (S.mu (assume_fix body)))
  =
  let m1 = S.mu body in
  let m2 = S.mu (assume_fix body) in
  introduce forall (is: E.stream input)
                   (orc: E.stream (SB.option_type_sem m1.oracle))
                   (n: nat).
      (let ios1 = S.with_oracle m1 is orc in
       let ios2 = S.with_oracle m2 is orc in
       S.stream_of_output m1.raw ios1 n == S.stream_of_output m2.raw ios2 n /\
       (S.stream_of_assumptions m1.raw ios1 n <==> S.stream_of_assumptions m2.raw ios2 n) /\
       (S.stream_of_obligations m1.raw ios1 n <==> S.stream_of_obligations m2.raw ios2 n))
  with begin
    let ios1 = S.with_oracle m1 is orc in
    let ios2 = S.with_oracle m2 is orc in
    assert (forall (k: nat). ios1 k == ios2 k);
    lemma_step_result_mu_af body.raw ios1 n;
    S.lemma_stream_of_output_congruence      m2.raw ios1 ios2 n;
    S.lemma_stream_of_assumptions_congruence m2.raw ios1 ios2 n;
    S.lemma_stream_of_obligations_congruence m2.raw ios1 ios2 n
  end
#pop-options

(* THE STRONG RULE.

   Premise: the body triple with the knot's fixpoint assumption in scope
   (via [assume_fix]) --- i.e. the body may assume [sofar(x = body)], which the
   ambient [sofar] delivers from the per-step assumption for free. Conclusion:
   the ordinary [mu] triple. No causal side-conditions beyond the weak rule's;
   at the system-triple level even those vanish. *)
let mu_strong
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (body: S.sys (output & input) output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      ES.causal p /\ ES.causal2 q /\
      L.triple (L.mu_body_pre p q) (assume_fix body) (L.mu_body_post q))
    (ensures L.triple p (S.mu body) q)
  =
  L.mu p (assume_fix body) q;
  lemma_equiv_mu_assume_fix body;
  SL.equiv_transport p (S.mu body) (S.mu (assume_fix body)) q

(*** Worked example: count = µx. (0 fby (x+1)), proved via [mu_strong] ***)

(* [assume_fix] keeps the body's output/obligations and adds the fixpoint
   assumption [x == output] to its assumptions. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec lemma_step_result_af
  (#input #output: Type)
  (#oracle #state: option Type)
  (t: SB.system (output & input) oracle state output)
  (ios: S.io_stream (output & input) oracle)
  (n: nat)
  : Lemma
    (ensures (
      let a = S.step_result_at (system_assume_fix t) ios n in
      let b = S.step_result_at t ios n in
      a.s == b.s /\
      a.v == b.v /\
      (SB.option_prop_sem a.chck.assumptions <==>
        ((fst (fst (ios n)) == b.v) /\ SB.option_prop_sem b.chck.assumptions)) /\
      (SB.option_prop_sem a.chck.obligations <==> SB.option_prop_sem b.chck.obligations)))
    (decreases n)
  =
  if n = 0 then () else lemma_step_result_af t ios (n - 1)
#pop-options

let lemma_af
  (#input #output: Type)
  (#oracle #state: option Type)
  (t: SB.system (output & input) oracle state output)
  (ios: S.io_stream (output & input) oracle)
  (n: nat)
  : Lemma
    (ensures (
      S.stream_of_output (system_assume_fix t) ios n == S.stream_of_output t ios n /\
      (S.stream_of_assumptions (system_assume_fix t) ios n <==>
        ((fst (fst (ios n)) == S.stream_of_output t ios n) /\ S.stream_of_assumptions t ios n)) /\
      (S.stream_of_obligations (system_assume_fix t) ios n <==> S.stream_of_obligations t ios n)))
  =
  lemma_step_result_af t ios n

(*** Safety: [mu_strong] subsumes [mu] (forgets no information) ***)

(* [mu_body_post] inherits [q]'s causality. *)
let lemma_mu_body_post_causal2
  (#input #output: Type)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma (requires ES.causal2 q) (ensures ES.causal2 (L.mu_body_post q))
  =
  introduce forall (xs1 xs2: E.stream (output & input))
                   (ys1 ys2: E.stream output) (n: nat).
      ((forall (k: nat). k <= n ==> xs1 k == xs2 k) ==>
       (forall (k: nat). k <= n ==> ys1 k == ys2 k) ==>
       (L.mu_body_post q xs1 ys1 n <==> L.mu_body_post q xs2 ys2 n))
  with introduce _ ==> _ with _. introduce _ ==> _ with _.
    ES.lemma_causal2_prefix q (L.source xs1) (L.source xs2) ys1 ys2 n

(* A triple about [body] transfers to [assume_fix body]: the wrapped system has
   the same output/obligations and *stronger* assumptions, so it can only be
   easier to satisfy. This is the crux of safety --- adding the fixpoint
   assumption never invalidates a body proof. *)
#push-options "--split_queries always --z3rlimit 150"
let lemma_triple_assume_fix
  (#input #output: Type)
  (p: E.stream (output & input) -> E.stream prop)
  (body: S.sys (output & input) output)
  (q: E.stream (output & input) -> E.stream output -> E.stream prop)
  : Lemma
    (requires ES.causal2 q /\ L.triple p body q)
    (ensures L.triple p (assume_fix body) q)
  =
  let afb = assume_fix body in
  let aux (is: E.stream (output & input))
          (orc: E.stream (SB.option_type_sem afb.oracle)) (n: nat)
    : Lemma
      (requires (let ios = S.with_oracle afb is orc in
                 ES.sofar (p is) n /\ ES.sofar (S.stream_of_assumptions afb.raw ios) n))
      (ensures (let ios = S.with_oracle afb is orc in
                let os = S.stream_of_output afb.raw ios in
                ES.sofar (q is os) n /\ ES.sofar (S.stream_of_obligations afb.raw ios) n))
    =
    let ios   = S.with_oracle afb is orc in
    let ios_b = S.with_oracle body is orc in
    assert (forall (k: nat). ios k == ios_b k);
    Classical.forall_intro (lemma_af body.raw ios);
    introduce forall (k: nat). S.stream_of_output body.raw ios k == S.stream_of_output body.raw ios_b k
      with S.lemma_stream_of_output_congruence body.raw ios ios_b k;
    introduce forall (k: nat). S.stream_of_assumptions body.raw ios k == S.stream_of_assumptions body.raw ios_b k
      with S.lemma_stream_of_assumptions_congruence body.raw ios ios_b k;
    introduce forall (k: nat). S.stream_of_obligations body.raw ios k == S.stream_of_obligations body.raw ios_b k
      with S.lemma_stream_of_obligations_congruence body.raw ios ios_b k;
    let os_b = S.stream_of_output body.raw ios_b in
    let os   = S.stream_of_output afb.raw ios in
    (* [afb]'s assumptions imply [body]'s, so the body triple fires. *)
    assert (ES.sofar (S.stream_of_assumptions body.raw ios_b) n);
    assert (ES.sofar (q is os_b) n /\ ES.sofar (S.stream_of_obligations body.raw ios_b) n);
    (* [os] and [os_b] agree pointwise; causality moves [q] across. *)
    ES.lemma_causal2_prefix q is is os_b os n
  in
  Classical.forall_intro_3 (fun is orc n -> Classical.move_requires (aux is orc) n)
#pop-options

(* SAFETY THEOREM: anything the weak rule [L.mu] proves, [mu_strong] proves too.
   So eagerly applying [mu_strong] never loses ground relative to [mu] --- it is
   the "safe" unfolding, retaining the fixpoint equation that [mu] discards. *)
let mu_from_strong
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (body: S.sys (output & input) output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      ES.causal p /\ ES.causal2 q /\
      L.triple (L.mu_body_pre p q) body (L.mu_body_post q))
    (ensures L.triple p (S.mu body) q)
  =
  lemma_mu_body_post_causal2 q;
  lemma_triple_assume_fix (L.mu_body_pre p q) body (L.mu_body_post q);
  mu_strong p body q

(* The counter body: [0 fby (x + 1)], where [x = fst input] is the recursive
   feedback. As a system over input [(int & unit)]. *)
let incr : S.sys (int & unit) int =
  S.map (fun (xi: int & unit) -> fst xi + 1) (S.id #(int & unit))

let counter_body : S.sys (int & unit) int = S.fby 0 incr

let count : S.sys unit int = S.mu counter_body

(* Precondition [True]; postcondition [output n == n]. *)
let cp : E.stream unit -> E.stream prop = fun _ -> (fun _ -> True)
let cq : E.stream unit -> E.stream int -> E.stream prop = fun _ os -> (fun n -> os n == n)

(* The strong-rule premise, discharged by 1-induction on the body. With
   [assume_fix]'s assumption in scope the proof may use the fixpoint equation
   [x_{n-1} = os_{n-1}] together with the body equation [os_n = x_{n-1} + 1].

   NOTE: [count = n] is NOT a genuine weak/strong separation --- see
   [lemma_count_weak] below. Because the postcondition [os = n] already *pins*
   the feedback, the weak rule's [pre(q x)] (i.e. [x_{n-1} = n-1]) is enough on
   its own. This example only demonstrates that [mu_strong] composes and
   verifies end-to-end on a real recursive program. In this total,
   deterministic setting weak Park induction is surprisingly complete for
   pinning-style properties; genuine separations need relational / mutual-
   recursion properties where [q] cannot determine the feedback. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300 --split_queries always"
let lemma_counter_vc (_: unit)
  : Lemma (L.induct1_vc (assume_fix counter_body) (L.mu_body_pre cp cq) (L.mu_body_post cq))
  =
  let afb = assume_fix counter_body in
  introduce forall (ixs: E.stream (int & unit))
                   (orc: E.stream (SB.option_type_sem afb.oracle))
                   (n: nat).
      (let ios = S.with_oracle afb ixs orc in
       let os  = S.stream_of_output afb.raw ios in
       (ES.sofar (L.mu_body_pre cp cq ixs) n /\
        ES.sofar (S.stream_of_assumptions afb.raw ios) n /\
        (forall (k: nat). k < n ==> L.mu_body_post cq ixs os k) /\
        (forall (k: nat). k < n ==> S.stream_of_obligations afb.raw ios k))
       ==>
       (L.mu_body_post cq ixs os n /\ S.stream_of_obligations afb.raw ios n))
  with introduce _ ==> _ with _. begin
    let ios = S.with_oracle afb ixs orc in
    (* [afb] output/assumptions in terms of [counter_body]. *)
    Classical.forall_intro (lemma_af counter_body.raw ios);
    (* [counter_body.raw == system_pre 0 incr.raw]; unfold [fby], [map], [id]. *)
    Classical.forall_intro (S.lemma_system_pre 0 incr.raw ios);
    Classical.forall_intro (S.lemma_map (fun (xi: int & unit) -> fst xi + 1) (S.id #(int & unit)) ios);
    Classical.forall_intro (S.lemma_system_project (fun (i: int & unit) -> i) ios);
    (* Expose the [sofar] hypotheses at every earlier step. *)
    ES.sofar_index (S.stream_of_assumptions afb.raw ios) n
  end
#pop-options

let lemma_count (_: unit)
  : Lemma (L.triple cp count cq)
  =
  assert (ES.causal cp);
  assert (ES.causal2 cq);
  lemma_counter_vc ();
  L.induct1 (assume_fix counter_body) (L.mu_body_pre cp cq) (L.mu_body_post cq);
  mu_strong cp counter_body cq

(* Honest check: the WEAK rule (plain [L.mu], no [assume_fix]) ALSO proves
   count = n --- the postcondition pins the feedback, so [pre(q x)] suffices and
   the fixpoint equation is not needed here. Kept as evidence that this example
   is a machinery demo, not a weak/strong separation. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300 --split_queries always"
let lemma_counter_vc_weak (_: unit)
  : Lemma (L.induct1_vc counter_body (L.mu_body_pre cp cq) (L.mu_body_post cq))
  =
  introduce forall (ixs: E.stream (int & unit))
                   (orc: E.stream (SB.option_type_sem counter_body.oracle))
                   (n: nat).
      (let ios = S.with_oracle counter_body ixs orc in
       let os  = S.stream_of_output counter_body.raw ios in
       (ES.sofar (L.mu_body_pre cp cq ixs) n /\
        ES.sofar (S.stream_of_assumptions counter_body.raw ios) n /\
        (forall (k: nat). k < n ==> L.mu_body_post cq ixs os k) /\
        (forall (k: nat). k < n ==> S.stream_of_obligations counter_body.raw ios k))
       ==>
       (L.mu_body_post cq ixs os n /\ S.stream_of_obligations counter_body.raw ios n))
  with introduce _ ==> _ with _. begin
    let ios = S.with_oracle counter_body ixs orc in
    Classical.forall_intro (S.lemma_system_pre 0 incr.raw ios);
    Classical.forall_intro (S.lemma_map (fun (xi: int & unit) -> fst xi + 1) (S.id #(int & unit)) ios);
    Classical.forall_intro (S.lemma_system_project (fun (i: int & unit) -> i) ios);
    ES.sofar_index (L.mu_body_pre cp cq ixs) n
  end
#pop-options

let lemma_count_weak (_: unit)
  : Lemma (L.triple cp count cq)
  =
  assert (ES.causal cp);
  assert (ES.causal2 cq);
  lemma_counter_vc_weak ();
  L.induct1 counter_body (L.mu_body_pre cp cq) (L.mu_body_post cq);
  L.mu cp counter_body cq
