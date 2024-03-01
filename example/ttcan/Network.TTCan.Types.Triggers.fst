module Network.TTCan.Types.Triggers

open Network.TTCan.Types.Base

module U64        = Network.TTCan.Prim.U64
module Subrange   = Network.TTCan.Prim.S32R

module List       = FStar.List.Tot

module UInt8      = FStar.UInt8
module UInt64     = FStar.UInt64
module Cast       = FStar.Int.Cast

open FStar.Mul

(* We assume a total, safe indexing function for triggers.
  The actual implementation will likely be backed by a read-only array. Since
  we only support at most 64 triggers, it doesn't really hurt to allocate space
  for all 64 of them.
*)
type trigger_index_fun = trigger_index -> trigger

(***** Non-streaming helper functions ****)
let trigger_check_enabled (cycle_index: cycle_index) (trigger: trigger): bool =
  let mask    = Subrange.pow2_minus_one trigger.repeat_factor in
  let mask8   = Subrange.s32r_to_u8 mask in
  let index8  = Subrange.s32r_to_u8 cycle_index in
  let offset8 = Subrange.s32r_to_u8 trigger.cycle_offset in
  UInt8.logand mask8 index8 = offset8

let trigger_tx_ref_expiry (tx_enable_window: tx_enable_window) (ix: trigger_index) (trigger: trigger): ntu =
  let open UInt64 in
  let tm = Subrange.s32r_to_u64 trigger.time_mark in
  tm +^ Subrange.s32r_to_u64 tx_enable_window

let trigger_offset (ref_trigger_offset: ref_offset) (tr: trigger): trigger =
  let time_mark =
    match tr.trigger_type with
    | Tx_Ref_Trigger ->
      // use saturating addition to clamp to [0,65535]
      Subrange.add_sat tr.time_mark ref_trigger_offset
    | _ ->
      tr.time_mark
  in
  { tr with time_mark }

(***** Requirements on trigger array ****)

(* Time-marks are sorted *)
let time_mark_sorted_all (trigger_read: trigger_index_fun): prop =
  forall (i: trigger_index).
    Subrange.v (trigger_read                   i).time_mark <=
    Subrange.v (trigger_read (Subrange.inc_sat i)).time_mark

(* Adequate time gap between triggers enabled on same cycle *)
let adequate_spacing (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config) (c: cycle_index) (i j: trigger_index): prop =
  Subrange.v i <= Subrange.v j                             ==>
  trigger_check_enabled c (trigger_read i) ==>
  trigger_check_enabled c (trigger_read j) ==>
  (Subrange.v (trigger_read i).time_mark - Subrange.v (trigger_read j).time_mark) >= (Subrange.v j - Subrange.v i) * Subrange.v ttcan_exec_period

let adequate_spacing_all (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config): prop =
  forall (c: cycle_index). forall (i j: trigger_index).
    adequate_spacing trigger_read ttcan_exec_period c i j

(* Adequate time gap from start of array to trigger *)
let time_mark_reachable_all (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config): prop =
  forall (i: trigger_index).
    Subrange.v i * Subrange.v ttcan_exec_period <= Subrange.v (trigger_read i).time_mark

(* Trigger configuration: the array as an index function, the period of
  execution frequency (eg once per 10µs), as well as the proofs that the array
  represents a valid schedule. *)
noeq
type triggers = {
  trigger_read: trigger_index_fun;
  ttcan_exec_period: ntu_config;

  time_mark_sorted_all: squash (time_mark_sorted_all trigger_read);
  adequate_spacing_all: squash (adequate_spacing_all trigger_read ttcan_exec_period);
  time_mark_reachable_all: squash (time_mark_reachable_all trigger_read ttcan_exec_period);
}

(* Compute the index of the next active trigger (specification only).
  This should be equivalent to the index with the minimum start time of all
  future enabled triggers. If no such triggers exist, it returns
  max_trigger_count (one past the end of the array).

  Note Specification Only
  -----------------------
  This function must not be called as executable code, as it would have the
  wrong complexity (linear in the number of triggers, rather than constant).
  We mark it as noextract so it can't be extracted. Really it should be ghost,
  but Pipit doesn't support ghost code yet.
  *)
noextract
let rec active_next_after_index (trigger_read: trigger_index_fun) (cycle_index: cycle_index) (time: nat) (index: nat { 0 <= index /\ index <= max_trigger_count })
  : Tot
    (n: nat { index <= n /\ n <= max_trigger_count })
    (decreases (max_trigger_count - index)) =
  if index >= max_trigger_count
  then max_trigger_count
  else
    let tr = trigger_read (Subrange.s32r index) in
    if Subrange.v tr.time_mark > time && trigger_check_enabled cycle_index tr
    then index
    else active_next_after_index trigger_read cycle_index time (index + 1)

(* Index of the next active trigger (specification only) *)
noextract
let active_next_after (trigger_read: trigger_index_fun) (cycle_index: cycle_index) (time: nat)
  : (n: nat { 0 <= n /\ n <= max_trigger_count }) =
  active_next_after_index trigger_read cycle_index time 0

(* Compute the index of the most-recent active trigger (specification only).
  This should be equivalent to the index with the maximum start time of all
  triggers whose start time is now or in the past. If no such triggers exist,
  it returns zero.
*)
noextract
let rec active_now_index (trigger_read: trigger_index_fun) (cycle_index: cycle_index) (time: nat) (index: nat { index < max_trigger_count })
  : Tot
    (n: nat { 0 <= n /\ n < max_trigger_count })
    (decreases index) =
  if index = 0
  then 0
  else
    let tr = trigger_read (Subrange.s32r index) in
    if Subrange.v tr.time_mark <= time && trigger_check_enabled cycle_index tr
    then index
    else active_now_index trigger_read cycle_index time (index - 1)

(* Index of the most-recent active trigger *)
noextract
let active_now (trigger_read: trigger_index_fun) (cycle_index: cycle_index) (time: nat)
  : (n: nat { 0 <= n /\ n < max_trigger_count }) =
  active_now_index trigger_read cycle_index time max_trigger_index


(* True if trigger will start before the end of this frame, or has already started *)
noextract
let trigger_started (triggers: triggers) (cycle_time: nat) (time_mark: nat): bool =
  time_mark <= cycle_time + Subrange.v triggers.ttcan_exec_period

(* True if trigger starts in this frame *)
noextract
let trigger_impending (triggers: triggers) (cycle_time: nat) (time_mark: nat): bool =
  cycle_time < time_mark && time_mark <= cycle_time + Subrange.v triggers.ttcan_exec_period


irreducible
let lemma_adequate_spacing_next_inc_pattern (triggers: triggers) (c: cycle_index) (time: ntu) (i: trigger_index) = ()

let lemma_adequate_spacing_next_inc
  (triggers: triggers) (c: cycle_index) (time: ntu) (i: trigger_index)
  : Lemma
    (ensures (
       let n = active_next_after_index triggers.trigger_read c (UInt64.v time) (Subrange.v i) in
       n < max_trigger_count ==>
       adequate_spacing triggers.trigger_read triggers.ttcan_exec_period i (Subrange.s32r n) c
    ))
    [SMTPat (lemma_adequate_spacing_next_inc_pattern triggers c time i)]
    = ()

// let trigger_index_invariant (cfg: config) (c: cycle) (now: time) (index: index): bool =
//   match next cfg.triggers index c with
//   | None -> true
//   | Some n -> (cfg.triggers.time_mark n - now) >= (n - index)

// let trigger_fetch_guar (cfg: config) (c: cycle) (index: stream int) (now: stream int): stream bool =
//   (index < cfg.triggers.size && trigger_enabled cfg index c) ==> trigger_time_mark cfg index >= now
