(* Worked example: prove  { True } (µx. 0 fby x) { x. x = 0 }.

   The induction is provided entirely by [Logic.mu]; [Logic.fby] contributes
   only the output shift, and the recursive variable [x] is read by the
   projection [System.map fst System.id]. *)
module Pipit.Extensional.Example

module E  = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module S  = Pipit.Extensional.System
module SB = Pipit.System.Base
module L  = Pipit.Extensional.Logic
module Classical = FStar.Classical

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

(*** Example 2:  { True } µx. (0 fby x) + 1 { x. x > 0 } ***)

(* The recursive body  (0 fby x) + 1  is an outer [map (+1)] over  0 fby x. *)
let fb0    : S.sys (int & unit) int = S.fby 0 t_x
let body2  : S.sys (int & unit) int = S.map (fun v -> v + 1) fb0
let prog2  : S.sys unit int         = S.mu body2

let q_pos : E.stream unit -> E.stream int -> E.stream prop = fun _ os -> (fun n -> os n > 0)

let p_pos      = L.mu_body_pre p_true q_pos
let q_post_pos = L.mu_body_post q_pos
(* [q_post_pos] shifted through [map (+1)] (the premise [Logic.map] leaves), then
   through [fby 0] (the premise [Logic.fby] leaves). *)
let q_map : E.stream (int & unit) -> E.stream int -> E.stream prop =
  fun is ot -> q_post_pos is (ES.map (fun v -> v + 1) ot)
let q_txpost : E.stream (int & unit) -> E.stream int -> E.stream prop =
  fun is ot -> q_map is (ES.fby 0 ot)

(* Body triple for the projection [t_x], with the postcondition shifted through
   both [map (+1)] and [fby 0]. *)
#push-options "--z3rlimit 50"
let lemma_t_x_triple2 (_: unit)
  : Lemma (L.triple p_pos t_x q_txpost)
  =
  let qid : E.stream (int & unit) -> E.stream (int & unit) -> E.stream prop =
    fun is ot -> q_txpost is (ES.map fst ot) in
  assert (ES.causal2 q_txpost);
  assert (ES.causal2 qid);
  introduce forall (is: E.stream (int & unit)) (n: nat).
      ES.sofar (p_pos is) n ==> ES.sofar (qid is is) n
    with introduce _ ==> _ with _.
      ES.sofar_index (p_pos is) n;
  L.id p_pos qid;
  L.map fst (S.id #(int & unit)) p_pos q_txpost
#pop-options

(* [map (+1)] and [fby 0] shift the body, [mu] closes the recursion. *)
let lemma_count_pos (_: unit)
  : Lemma (L.triple p_true prog2 q_pos)
  =
  assert (ES.causal p_true);
  assert (ES.causal2 q_pos);
  assert (ES.causal2 q_post_pos);
  assert (ES.causal2 q_map);
  lemma_t_x_triple2 ();
  L.fby 0 t_x p_pos q_map;
  L.map (fun v -> v + 1) fb0 p_pos q_post_pos;
  L.mu p_true body2 q_pos

(*** Example 1, oracle-free:  { True } µfby x. 0 fby x { x. x = 0 } ***)

(* Same specification as [lemma_zero_rec], but the recursion is closed by the
   oracle-free [mufby] combinator, so [prog_mufby] carries no oracle and is
   usable in specifications. [Logic.mufby]'s premise is [mu]'s premise for
   [delayed_body 0 t_x] (the mu-body that delays the guessed feedback). *)
let prog_mufby : S.sys unit int = S.mufby 0 t_x

let db1 : S.sys (int & unit) int = S.delayed_body 0 t_x

(* Body triple for [delayed_body 0 t_x]: it runs [t_x] on the delayed feedback,
   so its output is [0 fby feedback], which is zero on the guarded prefix. *)
let lemma_db1_aux
  (is_x: E.stream (int & unit))
  (orc_x: E.stream (SB.option_type_sem db1.oracle))
  (n: nat)
  : Lemma
    (requires
      ES.sofar (p_pre is_x) n /\
      ES.sofar (S.stream_of_assumptions db1.raw (S.with_oracle db1 is_x orc_x)) n)
    (ensures (
      let ios = S.with_oracle db1 is_x orc_x in
      let os  = S.stream_of_output db1.raw ios in
      ES.sofar (q_post is_x os) n /\
      ES.sofar (S.stream_of_obligations db1.raw ios) n))
  =
  let ios  = S.with_oracle db1 is_x orc_x in
  let dios = S.delayed_body_ios 0 t_x.raw ios in
  let os   = S.stream_of_output db1.raw ios in

  (* [delayed_body] unfold: [db1] runs [t_x] on the delayed-feedback io-stream. *)
  Classical.forall_intro (S.lemma_system_delayed_body 0 t_x.raw ios);
  (* [t_x = map fst id] outputs [fst] of its input; its checks are trivial. *)
  Classical.forall_intro (S.lemma_system_map_result fst (S.id #(int & unit)).raw dios);
  Classical.forall_intro (S.lemma_system_project (fun (i: int & unit) -> i) dios);
  assert (forall (k: nat). os k == ES.fby 0 (fun m -> fst (is_x m)) k);
  assert (forall (k: nat). S.stream_of_obligations db1.raw ios k == True);

  (* Expose the guarded precondition [pre (feedback = 0)] at every step. *)
  ES.sofar_index (p_pre is_x) n;
  assert (forall (k: nat). 0 < k /\ k <= n ==> fst (is_x (k - 1)) == 0);

  (* [0 fby feedback] is zero on the prefix: base at 0, step from the guard. *)
  assert (forall (k: nat). k <= n ==> os k == 0)

let lemma_db1_triple (_: unit)
  : Lemma (L.triple p_pre db1 q_post)
  =
  Classical.forall_intro_3
    (fun is orc n -> Classical.move_requires (lemma_db1_aux is orc) n)

(* The final proof: [mufby] closes the recursion without an oracle. *)
let lemma_zero_rec_mufby (_: unit)
  : Lemma (L.triple p_true prog_mufby q_zero)
  =
  assert (ES.causal p_true);
  assert (ES.causal2 q_zero);
  assert (ES.causal2 q_post);
  lemma_db1_triple ();
  L.mufby 0 t_x p_true q_zero

(*** Example 1, via mufby_step:  { True } mufby 0 t_x { x = 0 } ***)

(* Same result as [lemma_zero_rec_mufby], but discharged with the convenience
   rule [mufby_step]: the premise is a triple about [t_x] itself (fed the delayed
   feedback via [mufby_guard]), so no [delayed_body] unfold is written by hand. *)
#push-options "--z3rlimit 50"
let lemma_tx_step_triple (_: unit)
  : Lemma (L.triple (L.mufby_guard 0 p_true q_zero) t_x q_post)
  =
  let qid : E.stream (int & unit) -> E.stream (int & unit) -> E.stream prop =
    fun is ot -> q_post is (ES.map fst ot) in
  assert (ES.causal2 q_post);
  assert (ES.causal2 qid);
  introduce forall (is: E.stream (int & unit)) (n: nat).
      ES.sofar (L.mufby_guard 0 p_true q_zero is) n ==> ES.sofar (qid is is) n
    with introduce _ ==> _ with _.
      ES.sofar_index (L.mufby_guard 0 p_true q_zero is) n;
  L.id (L.mufby_guard 0 p_true q_zero) qid;
  L.map fst (S.id #(int & unit)) (L.mufby_guard 0 p_true q_zero) q_post
#pop-options

let lemma_zero_rec_mufby_step (_: unit)
  : Lemma (L.triple p_true prog_mufby q_zero)
  =
  assert (ES.causal p_true);
  assert (ES.causal2 q_zero);
  lemma_tx_step_triple ();
  L.mufby_step 0 t_x p_true q_zero
