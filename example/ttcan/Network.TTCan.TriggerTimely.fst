(* Simplified version of trigger fetch logic with timeliness proof.
  This abstracts some details of the trigger fetch itself:
  1. we ignore Ref_Trigger_Offset, which dynamically adjusts the time mark for
     Tx_Ref_Triggers by [-127,127];
  2. we use arbitrary-sized integer arithmetic for indices and times, which
     reduces some syntactic noise;
  3. we use a simple tick-based time instead of microseconds
*)
module Network.TTCan.TriggerTimely

module S     = Pipit.Sugar.Shallow

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module UInt8 = FStar.UInt8

type index = nat
(* Tick-based logical time; one message per tick *)
type time  = nat
(* Cycle index < 64 *)
type cycle = UInt8.t

(* Simple axiomatisation of read-only arrays. I don't think we can generate C code for this *)
noeq
type const_array (a: eqtype) = {
  get: index -> a;
  size: index;
}

type trigger = {
  (* When the trigger should start running *)
  time_mark:     time;
  (* Triggers are only enabled on certain cycles. *)
  (* Cycle_Mask is based on Repeat_Factor: cycle_mask = (1 << repeat_factor) - 1 *)
  cycle_mask:    cycle;
  (* Phase / offset *)
  cycle_offset:  cycle;

  // Missing:
  // trigger_type: Tx | Rx | Tx_Ref | Watch | ...
  // message_id: message_id // for Tx and Rx
}

(* Check if a trigger is enabled on a specific cycle index *)
let trigger_enabled (trigger: trigger) (cycle_index: cycle): bool =
  (UInt8.logand cycle_index trigger.cycle_mask) = trigger.cycle_offset

(*** Time-marks are sorted:
  The time-marks in an array must be *nondecreasingly* sorted. Duplicate
  time-marks are allowed, as long the two triggers are not enabled in the same
  cycle (formalised below).
*)
let time_mark_sorted_req (triggers: const_array trigger): prop =
  forall (i: index { i < triggers.size - 1 }).
    (triggers.get i).time_mark <= (triggers.get (i + 1)).time_mark


(*** Adequate spacing:
  If two triggers, i and j, are enabled in the same cycle, then their time
  marks must be far enough apart that we have time to iterate through the
  indices from i to j.
*)
let adequate_spacing (triggers: const_array trigger) (i j: index) (c: cycle): prop =
  i < triggers.size                  ==>
  j < triggers.size                  ==>
  i <= j                             ==>
  trigger_enabled (triggers.get i) c ==>
  trigger_enabled (triggers.get j) c ==>
  (triggers.get j).time_mark - (triggers.get i).time_mark >= (j - i)

let adequate_spacing_req (triggers: const_array trigger): prop =
  forall (i j: index). forall (c: cycle).
    adequate_spacing triggers i j c

(*** Time-marks are reachable from start:
  After a reset, we need to be able to get from index 0 to the first enabled
  time-mark i before it starts. This should hold in general too.
*)
let time_mark_reachable_req (triggers: const_array trigger): prop =
  forall (i: index { i < triggers.size }).
    i <= (triggers.get i).time_mark

(* Static trigger configuration, with proofs of the above properties *)
noeq
type config = {
  triggers: const_array trigger;
  time_mark_sorted_req:    time_mark_sorted_req triggers;
  adequate_spacing_req:    adequate_spacing_req triggers;
  time_mark_reachable_req: time_mark_reachable_req triggers;
}


(* Find next enabled trigger *)
let rec next (triggers: const_array trigger) (ix: index { ix < triggers.size }) (c: cycle)
  : Tot (j: index { ix <= j /\ j < triggers.size }) (decreases (triggers.size - ix)) =
  if trigger_enabled (triggers.get ix) c
  then ix
  else if ix < triggers.size - 1
  then next triggers (ix + 1) c
  else ix // reached end

let next_adequate_spacing (cfg: config) (i: index { i < cfg.triggers.size }) (c: cycle): prop =
  let n = next cfg.triggers i c in
  (cfg.triggers.get n).time_mark - (cfg.triggers.get i).time_mark >= (n - i)

let lemma_next_adequate_spacing (cfg: config) (i: index { i < cfg.triggers.size }) (c: cycle):
  Lemma (next_adequate_spacing cfg i c) =
  let n = next cfg.triggers i c in
  let the_forall: squash (forall (i j: index ) c. adequate_spacing cfg.triggers i j c) = cfg.adequate_spacing_req in
  eliminate forall (i: index ) (j: index) c. adequate_spacing cfg.triggers i j c
  with i n c;
  // assert (adequate_spacing cfg.triggers i (next cfg.triggers i c) c);
  admit ()

