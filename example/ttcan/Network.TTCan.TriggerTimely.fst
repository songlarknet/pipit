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
module Check     = Pipit.Sugar.Check
module T = Pipit.Tactics

module UInt8 = FStar.UInt8
// module UInt64 = FStar.UInt64

module Ints = Network.TTCan.Prim.IntUnsafe

// module U64S = Network.TTCan.Prim.U64

type index = nat
(* Tick-based logical time; one message per tick *)
type time  = int
(* Cycle index < 64 *)
type cycle = UInt8.t

(* Simple axiomatisation of read-only arrays. I don't think we can generate C code for this *)
noeq
type const_array (a: eqtype) = {
  get: int -> a;
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


instance has_stream_uint8: S.has_stream UInt8.t = {
  ty_id       = [`%UInt8.t];
  val_default = 0uy;
}

instance has_stream_trigger: S.has_stream trigger = {
  ty_id       = [`%trigger];
  val_default = { time_mark = S.val_default; cycle_mask = S.val_default; cycle_offset = S.val_default; };
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
  triggers: tr: const_array trigger { tr.size > 0 };
  time_mark_sorted_req:    squash (time_mark_sorted_req triggers);
  adequate_spacing_req:    squash (adequate_spacing_req triggers);
  time_mark_reachable_req: squash (time_mark_reachable_req triggers);
}


(* Find next enabled trigger, or triggers.size if none enabled *)
let rec next (triggers: const_array trigger) (ix: index { ix <= triggers.size }) (c: cycle)
  : Tot (j: index { ix <= j /\ j <= triggers.size /\ (trigger_enabled (triggers.get j) c \/ j == triggers.size)}) (decreases (triggers.size - ix)) =
  if trigger_enabled (triggers.get ix) c
  then ix
  else if ix < triggers.size - 1
  then next triggers (ix + 1) c
  else triggers.size // reached end

(* No enabled triggers remain *)
let next_none (cfg: config) (ix: index { ix < cfg.triggers.size }) (c: cycle): prop =
  next cfg.triggers ix c == cfg.triggers.size

let lemma_next_monotonic (triggers: const_array trigger) (ix: index { ix < triggers.size }) (c: cycle)
  : Lemma (next triggers ix c <= next triggers (ix + 1) c)
  = ()

let trigger_index_invariant (cfg: config) (c: cycle) (now: int) (index: int): prop =
  0 <= index /\ index <= cfg.triggers.size /\
  (let n = next cfg.triggers index c in
    n < cfg.triggers.size ==>
    (index < cfg.triggers.size /\ (cfg.triggers.get n).time_mark - now >= (n - index)))

let count_when_unchecked (max: index) (inc: S.stream bool): S.stream int =
  let open S in
  let open Ints in
  rec' (fun count ->
    check "" (const 0 <= count /\ count <= const max);^
    let^ count' = (0 `fby` count) + (if_then_else inc (const 1) (const 0)) in
    if_then_else (count' > const max) (const max) count')

let count_when (max: index): S.stream bool -> S.stream int =
  let e = Check.exp_of_stream1 (count_when_unchecked max) in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Network"]);
  Check.stream_of_checked1 e

let time_increasing (now: S.stream int): S.stream bool =
  let open S in
  let open Ints in
  // now = const 0 \/ 
  now = 0 `fby` (now + const 1)


let trigger_enabled' (tr: S.stream trigger) (c: cycle): S.stream bool =
  S.lift1 (fun t -> trigger_enabled t c) tr

let get_time_mark (tr: S.stream trigger): S.stream time =
  S.lift1 (fun t -> t.time_mark) tr

let trigger_index (cfg: config) (index: S.stream int): S.stream trigger =
  S.lift1 cfg.triggers.get index

let trigger_fetch_ctr (c: cycle) =
  let open S in
  let open Ints in
  Check.contract Pipit.Prim.Shallow.table [shallow int] (shallow trigger)
    (Check.exp_of_stream1 time_increasing)
    (Check.exp_of_stream2 (fun tr now -> trigger_enabled' tr c ==> get_time_mark tr >= now))

let assume_time_increasing: S.stream int -> S.stream unit =
  let e = Check.exp_of_stream1 (fun now -> S.check "" (time_increasing now)) in
  assume (Check.system_induct_k1 e);
  Check.stream_of_checked1 e

let trigger_fetch_unchecked (cfg: config) (c: cycle) (now: S.stream int): S.stream (trigger & int) =
  let open S in
  let open Ints in
  assume_time_increasing now;^
  rec' (fun trigger_ret ->
    let trigger = fst trigger_ret in
    let^ inc = false `fby` ((get_time_mark trigger <= now \/ ~ (trigger_enabled' trigger c))) in
    let^ index = count_when cfg.triggers.size inc in
    let^ trigger = trigger_index cfg index in

    check2 (fun now index -> trigger_index_invariant cfg c now index) now index;^
    tup trigger index)

let trigger_fetch (cfg: config) (c: cycle): S.stream int -> S.stream (trigger & int) =
  // unpacking cfg and triggers reduces a lot of matches in the generated goals; maybe simplify_products tactic chould break apart records too
  // match cfg with
  // | { triggers; time_mark_sorted_req; adequate_spacing_req; time_mark_reachable_req; } ->
  // match triggers with
  // | { get; size } ->
  //   let e = Check.exp_of_stream1 (trigger_fetch_unchecked { triggers = { get; size; }; time_mark_sorted_req; adequate_spacing_req; time_mark_reachable_req; } c) in
    let e = Check.exp_of_stream1 (trigger_fetch_unchecked cfg c) in
    let sys = Pipit.System.Exp.system_of_exp e in
    assert (Pipit.System.Ind.base_case sys) by (T.pipit_simplify_products ["Network.TTCan"]);
    assert (Pipit.System.Ind.step_case sys) by (T.pipit_simplify_products ["Network.TTCan"]);
    assert (Check.system_induct_k1 e);
    Check.stream_of_checked1 e

let trigger_fetch_spec_unchecked (cfg: config) (c: cycle) (now: S.stream int): S.stream (trigger & int) =
  let trigger_max_index: index = cfg.triggers.size - 1 in
  let open S in
  let open Ints in
  let^ trigger_ret = trigger_fetch cfg c now in
  let^ trigger = fst trigger_ret in
  let^ index = snd trigger_ret in
  let^ new_trigger = index <> (-1) `fby` index in
  check "" (
    (new_trigger /\ trigger_enabled' trigger c /\ index < const cfg.triggers.size) ==>
    get_time_mark trigger >= now);^
  trigger_ret

let trigger_fetch_spec (cfg: config) (c: cycle): S.stream int -> S.stream (trigger & int) =
  let e = Check.exp_of_stream1 (trigger_fetch_unchecked cfg c) in
  let sys = Pipit.System.Exp.system_of_exp e in
  assert (Pipit.System.Ind.base_case sys) by (T.pipit_simplify_products ["Network.TTCan"]);
  assert (Pipit.System.Ind.step_case sys) by (T.pipit_simplify_products ["Network.TTCan"]);
  assert (Check.system_induct_k1 e);
  Check.stream_of_checked1 e
