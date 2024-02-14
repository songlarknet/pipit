module Network.TTCan.Impl.Triggers

module S     = Pipit.Sugar.Shallow
module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked
module Util  = Network.TTCan.Impl.Util

open Network.TTCan.Types

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

open Pipit.Sugar.Shallow.Tactics.Lift

module UInt8 = FStar.UInt8
module UInt64= FStar.UInt64
module Cast  = FStar.Int.Cast

(***** Non-streaming helper functions ****)
let trigger_check_enabled (cycle_index: cycle_index) (trigger: trigger): bool =
  let mask    = S32R.pow2_minus_one trigger.repeat_factor in
  let mask8   = S32R.s32r_to_u8 mask in
  let index8  = S32R.s32r_to_u8 cycle_index in
  let offset8 = S32R.s32r_to_u8 trigger.cycle_offset in
  UInt8.logand mask8 index8 = offset8

let trigger_compute_expiry (cfg: config) (ix: trigger_index) (trigger: trigger): ntu =
  let open UInt64 in
  let tm = S32R.s32r_to_u64 trigger.time_mark in
  (* We keep trying to send Tx_Ref_Triggers until they're pre-empted by the next trigger, so their expiry is very large.
    We keep trying to send Tx_Triggers for Tx_Enable_Window ntus.
    We don't need to keep trying Rx_Triggers or Watch_Triggers. *)
  match trigger.trigger_type with
  | Tx_Ref_Trigger ->
    tm +^ 65535uL
  | Tx_Trigger ->
    tm +^ S32R.s32r_to_u64 cfg.tx_enable_window
  | _ ->
    tm


let trigger_load (cfg: config) (ix: trigger_index) (ref_trigger_offset: ref_offset): trigger =
  [@@no_inline_let] // do not inline index function into use-sites
  let base = cfg.trigger_index_fun ix in
  let time_mark =
    match base.trigger_type with
    | Tx_Ref_Trigger ->
      // use saturating addition to clamp to [0,65535]
      S32R.add_sat base.time_mark ref_trigger_offset
    | _ ->
      base.time_mark
  in
  { base with time_mark }

(* Result of pre-fetch node *)
type prefetch_result = {
  index:   trigger_index;
  // True when trigger is enabled in current basic cycle index
  enabled: bool;
  // Trigger end time: when to give up trying for triggers with retries (Tx_Message and Tx_Ref_Message)
  expiry:  ntu;
  // Trigger information
  trigger: trigger;
}

type fetch_result = {
  current:    prefetch_result;
  // True when trigger changes
  is_new:     bool;
  // True if trigger's start time <= now
  is_started: bool;
  // True if trigger's end time <= now
  is_expired: bool;
  // Total enabled and disabled triggers seen this cycle
  tx_count:   trigger_count;
}


(**** Streaming instances for records ****)
instance has_stream_prefetch_result: S.has_stream prefetch_result = {
  ty_id       = [`%prefetch_result];
  val_default = { enabled = S.val_default; index = S.val_default; expiry = S.val_default; trigger = S.val_default; };
}

instance has_stream_fetch_result: S.has_stream fetch_result = {
  ty_id       = [`%fetch_result];
  val_default = { current = S.val_default; is_new = S.val_default;  is_started = S.val_default; is_expired = S.val_default; tx_count = S.val_default; };
}

(*
  Pre-fetch the next enabled trigger.
  This node loops through the triggers array. At each tick, it checks if the current trigger is disabled or has passed its start time. If so, it increments the index and progresses to the next trigger. Once the index reaches the end of the array, the index remains at the last value until reset_ck becomes true.
  The time marks in the trigger array must be ascending, and must have large enough gaps to allow the prefetcher to skip over disabled triggers.
  For example, if the prefetch executes every 10 ntus, then a configuration with a gap of 10ntus between
  > [ Tx_Trigger { Time_Mark = 0, Cycle_Offset = 0, Repeat_Factor = 1, Message = A };
  >   Tx_Trigger { Time_Mark = 10, Cycle_Offset = 0, Repeat_Factor = 2, Message = B };
  >   Tx_Trigger { Time_Mark = 10, Cycle_Offset = 1, Repeat_Factor = 2, Message = C } ]
  should result in a sequence like `AB...AC...AB...AC...`
  but there isn't a long enough gap after A to skip over the B and reach the C.

  Invariant: all trigger entries before trigger_index have start time in the past or are not enabled this cycle.
*)
let prefetch
  (cfg: config)
  (reset_ck:           stream bool)
  (cycle_time:         stream ntu)
  // XXX: why #_ necessary?
  (cycle_index:        stream cycle_index #_)
  (ref_trigger_offset: stream ref_offset #_)
    : stream prefetch_result #_ =
  rec' (fun fetch ->
    let pre_index = (S32R.s32r 0 <: trigger_index) `fby` fetch.index in
    let advance = false `fby` (not fetch.enabled || U64.(S32R.s32r_to_u64 fetch.trigger.time_mark <= cycle_time)) in
    let index =
      if reset_ck
      then S32R.s32r 0
      else if advance
      then S32R.inc_sat pre_index
      else pre_index in
    let trigger = trigger_load cfg index ref_trigger_offset in
    let enabled = trigger_check_enabled cycle_index trigger in
    let expiry  = trigger_compute_expiry cfg index trigger in
    { index; enabled; expiry; trigger })

%splice[] (autolift_binds [`%prefetch])

(*^5.1 Tx_Count: each time a Tx_Trigger becomes active, Tx_Count is incremented. Tx_Count is not incremented beyond Expected_Tx_Trigger. *)
(* CLARIFICATION: the definition of "active" is not entirely clear to me.
  Is it whenever a Tx_Trigger trigger array entry is encountered by the trigger loop, or is it only when the trigger is enabled for the current cycle index?
  I think it must be every time it's encountered by the loop, because otherwise we would underflow for a periodic trigger that doesn't transmit every cycle.
  *)
let tx_counter
  (reset_ck: stream bool)
  (prefetch: stream prefetch_result #_)
    : stream trigger_count #_ =
  let open S32R in
  rec' (fun tx_count ->
    let prev: trigger_count =
      if reset_ck
      then s32r 0
      else s32r 0 `fby` tx_count in
    let incr =
      Util.edge #trigger_index prefetch.index &&
      prefetch.trigger.trigger_type = Tx_Trigger in
    if incr
    then inc_sat prev
    else prev)

%splice[] (autolift_binds [`%tx_counter])

(*
  Fetch the current trigger, or the next one if there is no current trigger.
*)
let fetch
  (cfg: config)
  (reset_ck:    stream bool)
  (cycle_time:  stream ntu)
  (cycle_index: stream cycle_index #_)
  (ref_trigger_offset: stream ref_offset #_)
    : stream fetch_result #_ =
  let is_trigger_started (tr: stream trigger #_): stream bool =
    U64.(S32R.s32r_to_u64 tr.time_mark <= cycle_time) in
  let next = prefetch cfg reset_ck cycle_time cycle_index ref_trigger_offset in
  rec' (fun (fetch: stream fetch_result #_) ->
    // If the new trigger is enabled and is ready to start, then the new trigger has precedence. This case allows Watch_Triggers to pre-empt Tx_Ref_Triggers, as Tx_Ref_Triggers do not expire otherwise.
    // Otherwise, if the old trigger expired on the previous tick, then we the new trigger can be started. The delay here ensures that the caller gets a chance to handle the expired triggers.
    let advance = reset_ck ||
      (next.enabled && is_trigger_started next.trigger) ||
      (false `fby` fetch.is_expired)
    in
    let current =
      next ->^ (if advance then next else pre fetch.current)
    in

    let index = current.index in
    let is_new = Util.edge #trigger_index index in
    let is_started = is_trigger_started current.trigger in
    let is_expired = U64.(current.expiry <= cycle_time) in
    let tx_count = tx_counter reset_ck next in
    { current; is_new; is_started; is_expired; tx_count; }
  )

%splice[] (autolift_binds [`%fetch])