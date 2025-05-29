module Network.TTCan.Types.Triggers

open Network.TTCan.Types.Base

module Schedule = Network.TTCan.Abstract.Schedule

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
  assert_norm ((Int.pow2_n #8 6 - 1) <= 255);
  let mask8   = Subrange.s32r_to_u8 mask in
  let index8  = Subrange.s32r_to_u8 cycle_index in
  let offset8 = Subrange.s32r_to_u8 trigger.cycle_offset in
  UInt8.logand mask8 index8 = offset8

let trigger_tx_ref_expiry (tx_enable_window: tx_enable_window) (ix: trigger_index) (trigger: trigger): ntu =
  let open UInt64 in
  let tm = Subrange.s32r_to_u64 trigger.time_mark in
  tm +^ Subrange.s32r_to_u64 tx_enable_window

let trigger_offset_time_mark (trigger: trigger) (ref_trigger_offset: ref_offset): ntu_config =
  match trigger.trigger_type with
  | Tx_Ref_Trigger ->
    Subrange.add_sat trigger.time_mark ref_trigger_offset
  | _ ->
    trigger.time_mark

type abstract_cycle = { cycle_index: cycle_index; ref_trigger_offset: ref_offset; }

let abstract_of_trigger (trigger: trigger): Schedule.event_info abstract_cycle =
  {
    enabled = (fun c -> trigger_check_enabled c.cycle_index trigger);
    time_mark = (fun c -> Subrange.v (trigger_offset_time_mark trigger c.ref_trigger_offset));
    time_mark_min = Subrange.v (trigger_offset_time_mark trigger (Subrange.s32r (-127)));
    time_mark_max = Subrange.v (trigger_offset_time_mark trigger (Subrange.s32r (127)));
    ok = ();
  }

let abstract_of_triggers
  (trigger_read: trigger_index_fun)
  (exec_period: ntu_config_pos)
  : Schedule.events abstract_cycle = {
    count = max_trigger_count;
    read  = (fun i -> abstract_of_trigger (trigger_read (Subrange.s32r i)));
    exec_period = Subrange.v exec_period;
  }

(* Trigger configuration: the array as an index function, the period of
  execution frequency (eg once per 10µs), as well as the proofs that the array
  represents a valid schedule. *)
noeq
type triggers = {
  trigger_read: trigger_index_fun;
  ttcan_exec_period: ntu_config_pos;

  // The user must provide a proof/witness that the abstract schedule is valid.
  // Probably we should have a check specific to the concrete events,
  // but this is good enough for now.
  schedule_is_valid: squash
    (Schedule.events_valid_req (abstract_of_triggers trigger_read ttcan_exec_period));
}
