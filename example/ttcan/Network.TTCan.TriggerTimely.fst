(* Simplified version of trigger fetch logic with timeliness proof.
  This abstracts some details of the trigger fetch itself:
  1. we ignore Ref_Trigger_Offset, which dynamically adjusts the time mark for
     Tx_Ref_Triggers by [-127,127];
  2. we use arbitrary-sized integer arithmetic for indices and times, which
     reduces some syntactic noise;
  3. we use a simple tick-based time instead of microseconds;
  4. no reset trigger;
  5. cycle offset is assumed constant (rather than taking a new value every reset)
*)
module Network.TTCan.TriggerTimely
#push-options "--print_bound_var_types --print_full_names"

module S     = Pipit.Sugar.Shallow

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics
module Check     = Pipit.Sugar.Check
module T = Pipit.Tactics

module Ints = Network.TTCan.Prim.IntUnsafe

type index = int
(* Tick-based logical time; one message per tick *)
type time  = int
(* Cycle index < 64 *)
type cycle = int

noeq
type trigger_array = {
  size:      nat;
  enabled:   index -> cycle -> bool;
  time_mark: index -> time;
}

(*** Time-marks are sorted:
  The time-marks in an array must be *nondecreasingly* sorted. Duplicate
  time-marks are allowed, as long the two triggers are not enabled in the same
  cycle (formalised below).
*)
let time_mark_sorted_req (triggers: trigger_array): prop =
  forall (i: index { i < triggers.size - 1 }).
    triggers.time_mark i <= triggers.time_mark (i + 1)

(*** Adequate spacing:
  If two triggers, i and j, are enabled in the same cycle, then their time
  marks must be far enough apart that we have time to iterate through the
  indices from i to j.
*)
let adequate_spacing (triggers: trigger_array) (i j: nat) (c: cycle): prop =
  i < triggers.size                  ==>
  j < triggers.size                  ==>
  i <= j                             ==>
  triggers.enabled i c               ==>
  triggers.enabled j c               ==>
  (triggers.time_mark j - triggers.time_mark i) >= (j - i)

let adequate_spacing_req (triggers: trigger_array): prop =
  forall (i j: nat). forall (c: cycle).
    adequate_spacing triggers i j c

(*** Time-marks are reachable from start:
  After a reset, we need to be able to get from index 0 to the first enabled
  time-mark i before it starts. This should hold in general too.
*)
let time_mark_reachable_req (triggers: trigger_array): prop =
  forall (i: index { 0 <= i /\ i < triggers.size }).
    i <= triggers.time_mark i

(* Static trigger configuration with proofs of the above properties *)
noeq
type config = {
  triggers:                trigger_array;
  time_mark_sorted_req:    squash (time_mark_sorted_req triggers);
  adequate_spacing_req:    squash (adequate_spacing_req triggers);
  time_mark_reachable_req: squash (time_mark_reachable_req triggers);
  size_req:                squash (triggers.size > 0);
}


(* Find next enabled trigger or None *)
let rec next (triggers: trigger_array) (ix: int) (c: cycle)
  : Tot (option (j: index { j < triggers.size /\ (triggers.enabled j c) /\ ix <= j })) (decreases (triggers.size - ix)) =
  if ix < 0 || ix >= triggers.size
  then None
  else if triggers.enabled ix c
  then Some ix
  else (
    match next triggers (ix + 1) c with
    | Some i -> Some i
    | None -> None
  )

let trigger_index_invariant (cfg: config) (c: cycle) (now: time) (index: index): bool =
  match next cfg.triggers index c with
  | None -> true
  | Some n -> (cfg.triggers.time_mark n - now) >= (n - index)

let trigger_index_invariant_base (cfg: config) (c: cycle)
  : Lemma (trigger_index_invariant cfg c 0 0) =
  ()

let trigger_index_invariant_stay (cfg: config) (c: cycle) (now: int) (index: int)
  : Lemma (
      (trigger_index_invariant cfg c now index /\
      cfg.triggers.enabled index c /\
      cfg.triggers.time_mark index > now)
    ==>
      (trigger_index_invariant cfg c (now + 1) index)) =
  ()

let lemma_adequate_spacing_next_inc_def (cfg: config) (c: cycle) (index: index) =
  match next cfg.triggers (index + 1) c with
  | None -> True
  | Some n ->
    0 <= index ==>
    adequate_spacing cfg.triggers index n c

let lemma_adequate_spacing_next_inc (cfg: config) (c: cycle)
  : Lemma (forall (index: index). lemma_adequate_spacing_next_inc_def cfg c index)
  = ()

let trigger_index_invariant_step (cfg: config) (c: cycle) (now: int) (index: int)
  : Lemma (
      (0 <= index /\ trigger_index_invariant cfg c now index)
    ==>
      trigger_index_invariant cfg c (now + 1) (index + 1)) =
  match next cfg.triggers (index + 1) c with
  | None -> ()
  | Some n' -> lemma_adequate_spacing_next_inc cfg c

let pose_trigger_index_invariant_zero (cfg: config) (c: cycle): S.stream unit =
  S.pose (trigger_index_invariant cfg c 0 0)
    ()

let pose_trigger_index_invariant_stay (cfg: config) (c: cycle) (now: S.stream int) (index: S.stream int): S.stream unit =
  S.pose2 (fun now index ->
      (trigger_index_invariant cfg c now index /\
      cfg.triggers.enabled index c /\
      cfg.triggers.time_mark index > now)
    ==>
      (trigger_index_invariant cfg c (now + 1) index))
    (fun now index -> trigger_index_invariant_stay cfg c now index)
    now index

let pose_trigger_index_invariant_step (cfg: config) (c: cycle) (now: S.stream int) (index: S.stream int): S.stream unit =
  S.pose2
    (fun now index -> (0 <= index /\ trigger_index_invariant cfg c now index) ==> trigger_index_invariant cfg c (now + 1) (index + 1))
    (fun now index -> trigger_index_invariant_step cfg c now index) now index

let count_when_unchecked (max: nat) (inc: S.stream bool): S.stream int =
  let open S in
  let open Ints in
  rec' (fun count ->
    check "" (const 0 <= count /\ count <= const max);^
    let^ count' = (0 `fby` count) + (if_then_else inc (const 1) (const 0)) in
    if_then_else (count' > const max) (const max) count')

let count_when (max: nat): S.stream bool -> S.stream int =
  let e = Check.exp_of_stream1 (count_when_unchecked max) in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Network"]);
  Check.stream_of_checked1 e

let time_increasing (now: S.stream int): S.stream bool =
  let open S in
  let open Ints in
  // now = const 0 \/ 
  now = 0 `fby` (now + const 1)


let trigger_enabled (cfg: config) (index: S.stream index) (c: cycle): S.stream bool =
  S.lift1 (fun index -> cfg.triggers.enabled index c) index

let trigger_time_mark (cfg: config) (index: S.stream index): S.stream time =
  S.lift1 (fun index -> cfg.triggers.time_mark index) index


let trigger_fetch_unchecked (cfg: config) (c: cycle) (now: S.stream time): S.stream (index & bool) #_ =
  let open S in
  let open Ints in
  rec' (fun index_intr ->
    let^ index = fst index_intr in
    let^ inc = false `fby` ((trigger_time_mark cfg index <= now \/ ~ (trigger_enabled cfg index c))) in
    let^ index = count_when cfg.triggers.size inc in
    let^ interrupt = inc /\ index < const cfg.triggers.size /\ trigger_enabled cfg index c in

    pose1_forall (fun i -> lemma_adequate_spacing_next_inc_def cfg c i) () index;^
    check "" (sofar (time_increasing now) ==> (lift2 (fun now index -> trigger_index_invariant cfg c now index)) now index);^
    // pose_trigger_index_invariant_zero cfg c;^
    // pose_trigger_index_invariant_stay cfg c now index;^
    // pose_trigger_index_invariant_step cfg c now index;^
    tup index interrupt)


let trigger_fetch (cfg: config) (c: cycle): S.stream time -> S.stream (index & bool) #_ =
  let e = Check.exp_of_stream1 (trigger_fetch_unchecked cfg c) in
  let sys = Pipit.System.Exp.system_of_exp e in
  // assert (Pipit.System.Ind.base_case sys) by (T.clear_all (); T.pipit_simplify_products ["Network.TTCan"]; T.dump "base");
  // assert (Pipit.System.Ind.step_case sys) by (T.clear_all (); T.pipit_simplify_products ["Network.TTCan"]; T.dump "step");
  assert (Check.system_induct_k1 e) by (T.clear_all (); T.pipit_simplify_products ["Network.TTCan"]; T.dump "check");
  Check.stream_of_checked1 e


// let trigger_fetch_ctr (c: cycle) =
//   let open S in
//   let open Ints in
//   Check.contract Pipit.Prim.Shallow.table [shallow time] (shallow index)
//     (Check.exp_of_stream1 time_increasing)
//     (Check.exp_of_stream2 (fun index now -> trigger_enabled index c ==> trigger_time_mark index >= now))


// let trigger_fetch_spec_unchecked (cfg: config) (c: cycle) (now: S.stream int): S.stream (trigger & int) =
//   let trigger_max_index: index = cfg.triggers.size - 1 in
//   let open S in
//   let open Ints in
//   let^ trigger_ret = trigger_fetch cfg c now in
//   let^ trigger = fst trigger_ret in
//   let^ index = snd trigger_ret in
//   let^ new_trigger = index <> (-1) `fby` index in
//   check "" (
//     (new_trigger /\ trigger_enabled' trigger c /\ index < const cfg.triggers.size) ==>
//     get_time_mark trigger >= now);^
//   trigger_ret

// let trigger_fetch_spec (cfg: config) (c: cycle): S.stream int -> S.stream (trigger & int) =
//   let e = Check.exp_of_stream1 (trigger_fetch_unchecked cfg c) in
//   let sys = Pipit.System.Exp.system_of_exp e in
//   assert (Pipit.System.Ind.base_case sys) by (T.pipit_simplify_products ["Network.TTCan"]);
//   assert (Pipit.System.Ind.step_case sys) by (T.pipit_simplify_products ["Network.TTCan"]);
//   assert (Check.system_induct_k1 e);
//   Check.stream_of_checked1 e
