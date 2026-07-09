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

(* Body triple for the projection [t_x], with [q_post] post-composed with the
   [fby 0] shift (the premise [Logic.fby] needs). *)
let lemma_t_x_aux
  (is_x: E.stream (int & unit))
  (orc_x: E.stream (SB.option_type_sem t_x.oracle))
  (n: nat)
  : Lemma
    (requires
      ES.sofar (p_pre is_x) n /\
      ES.sofar (S.stream_of_assumptions t_x.raw (S.with_oracle t_x is_x orc_x)) n)
    (ensures (
      let ios = S.with_oracle t_x is_x orc_x in
      let os  = S.stream_of_output t_x.raw ios in
      ES.sofar (q_post is_x (ES.fby 0 os)) n /\
      ES.sofar (S.stream_of_obligations t_x.raw ios) n))
  =
  let ios = S.with_oracle t_x is_x orc_x in
  let os  = S.stream_of_output t_x.raw ios in

  (* [t_x = map fst id] outputs [fst input]; its checks are trivial. *)
  Classical.forall_intro (S.lemma_system_map_result fst (S.id #(int & unit)).raw ios);
  Classical.forall_intro (S.lemma_system_project (fun (i: int & unit) -> i) ios);
  assert (forall (k: nat). os k == fst (is_x k));
  assert (forall (k: nat). S.stream_of_obligations t_x.raw ios k == True);

  (* Expose the guarded precondition at every step. *)
  ES.sofar_index (p_pre is_x) n;
  assert (forall (k: nat). 0 < k /\ k <= n ==> fst (is_x (k - 1)) == 0);

  (* [0 fby os] is zero on the prefix: base at 0, step from the precondition. *)
  assert (forall (k: nat). k <= n ==> (ES.fby 0 os) k == 0)

let lemma_t_x_triple (_: unit)
  : Lemma (L.triple p_pre t_x (fun is ot -> q_post is (ES.fby 0 ot)))
  =
  Classical.forall_intro_3
    (fun is orc n -> Classical.move_requires (lemma_t_x_aux is orc) n)

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
let lemma_t_x_aux2
  (is_x: E.stream (int & unit))
  (orc_x: E.stream (SB.option_type_sem t_x.oracle))
  (n: nat)
  : Lemma
    (requires
      ES.sofar (p_pos is_x) n /\
      ES.sofar (S.stream_of_assumptions t_x.raw (S.with_oracle t_x is_x orc_x)) n)
    (ensures (
      let ios = S.with_oracle t_x is_x orc_x in
      let os  = S.stream_of_output t_x.raw ios in
      ES.sofar (q_txpost is_x os) n /\
      ES.sofar (S.stream_of_obligations t_x.raw ios) n))
  =
  let ios = S.with_oracle t_x is_x orc_x in
  let os  = S.stream_of_output t_x.raw ios in

  Classical.forall_intro (S.lemma_system_map_result fst (S.id #(int & unit)).raw ios);
  Classical.forall_intro (S.lemma_system_project (fun (i: int & unit) -> i) ios);
  assert (forall (k: nat). os k == fst (is_x k));
  assert (forall (k: nat). S.stream_of_obligations t_x.raw ios k == True);

  ES.sofar_index (p_pos is_x) n;
  assert (forall (k: nat). 0 < k /\ k <= n ==> fst (is_x (k - 1)) > 0);

  (* [(0 fby os) + 1] is positive on the prefix: base 0+1=1, step feedback+1. *)
  assert (forall (k: nat). k <= n ==> ((ES.fby 0 os) k + 1) > 0);
  assert (ES.sofar (q_txpost is_x os) n)

let lemma_t_x_triple2 (_: unit)
  : Lemma (L.triple p_pos t_x q_txpost)
  =
  Classical.forall_intro_3
    (fun is orc n -> Classical.move_requires (lemma_t_x_aux2 is orc) n)

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
