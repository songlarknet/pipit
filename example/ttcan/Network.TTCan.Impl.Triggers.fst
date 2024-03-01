module Network.TTCan.Impl.Triggers

module S     = Pipit.Sugar.Shallow
module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked
module Util  = Network.TTCan.Impl.Util

open Network.TTCan.Types

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics
module Contract  = Pipit.Sugar.Contract
module T = Pipit.Tactics

open Pipit.Sugar.Shallow.Tactics.Lift

module Tac = FStar.Tactics

module UInt64 = FStar.UInt64

(* Cycle and time information required by fetch and prefetch *)
type trigger_input = {
  reset_ck:           bool;
  cycle_time:         ntu;
  cycle_index:        cycle_index;
  ref_trigger_offset: ref_offset;
}

(* Result of pre-fetch node *)
type prefetch_result = {
  index:     trigger_index;
  // True when trigger is enabled in current basic cycle index
  enabled:   bool;
  // Updated time (after ref-trigger-offset applied to tx-ref triggers)
  time_mark: ntu_config;
}

type fetch_result = {
  current:    prefetch_result;
  trigger_type: trigger_type;
  message_index: can_buffer_id;
}


(**** Streaming instances for records ****)
instance has_stream_trigger_input: S.has_stream trigger_input = {
  ty_id       = [`%trigger_input];
  val_default = { reset_ck = S.val_default; cycle_time = S.val_default; cycle_index = S.val_default; ref_trigger_offset = S.val_default; };
}

instance has_stream_prefetch_result: S.has_stream prefetch_result = {
  ty_id       = [`%prefetch_result];
  val_default = { enabled = S.val_default; index = S.val_default; time_mark = S.val_default; };
}

instance has_stream_fetch_result: S.has_stream fetch_result = {
  ty_id       = [`%fetch_result];
  val_default = { current = S.val_default; trigger_type = S.val_default; message_index = S.val_default; };
}

(**** Non-streaming helper functions ****)
let trigger_load (cfg: config) (ix: trigger_index) (ref_trigger_offset: ref_offset): trigger =
  // do not inline index function into use-sites for extraction
  // XXX: this should not be necessary if we ensure extraction doesn't inline trigger_load / trigger_offset
  [@@no_inline_let]
  let base = cfg.triggers.trigger_read ix in
  trigger_offset ref_trigger_offset base

(* True if trigger will start before the end of this frame or has already started:
  > time_mark in [0, T+period]
 *)
let is_started (cfg: config) (cycle_time: ntu) (time_mark: ntu_config): bool =
  let open UInt64 in
  let time_mark = S32R.s32r_to_u64 time_mark in
  let ttcan_exec_period = S32R.s32r_to_u64 cfg.triggers.ttcan_exec_period in
  // TODO:OPT: because cycle_time: ntu uses full 64-bit, need to avoid overflow. cycle_time shouldn't need 64 bits.
  if time_mark <^ ttcan_exec_period
  then true
  else time_mark -^ ttcan_exec_period <=^ cycle_time

(* True if trigger will start in this frame:
  > time_mark in (T, T+period] *)
let is_impending (cfg: config) (cycle_time: ntu) (time_mark: ntu_config): bool =
  let open UInt64 in
  let time_mark = S32R.s32r_to_u64 time_mark in
  let ttcan_exec_period = S32R.s32r_to_u64 cfg.triggers.ttcan_exec_period in
  if time_mark <^ ttcan_exec_period
  then cycle_time <^ time_mark
  else cycle_time <^ time_mark && (time_mark -^ ttcan_exec_period <=^ cycle_time)

(* Sanity checks for is_started and is_impending
  These could just be refinements on the above, but the autolift tactic
  doesn't yet support refinements -- whoops. *)
let lemma_is_started (cfg: config) (cycle_time: ntu) (time_mark: ntu_config)
  : Lemma (ensures (
      is_started cfg cycle_time time_mark ==
      trigger_started cfg.triggers (UInt64.v cycle_time) (S32R.v time_mark)
  )) = ()

let lemma_is_impending (cfg: config) (cycle_time: ntu) (time_mark: ntu_config)
  : Lemma (ensures (
      is_impending cfg cycle_time time_mark ==
      trigger_impending cfg.triggers (UInt64.v cycle_time) (S32R.v time_mark)
  )) = ()

let trigger_absolute_time
  (local_time: ntu)
  (cycle_time: ntu)
  (time_mark:  ntu_config)
             : ntu =
  let open UInt64 in
  let time_mark  = S32R.s32r_to_u64 time_mark in
  // TODO: use checked arithmetic:
  // assert (cycle_time <= time_mark);
  // assert (local_time <= 2^62);
  // assert (cycle_time <= local_time);
  let diff       = time_mark -%^ cycle_time in
  let diff_mark  = local_time +%^ diff in
  // assert (UInt64.v diff_mark == UInt64.v local_time + (UInt64.v time_mark - UInt64.v cycle_time));
  diff_mark

(**** Specification ****)

(* Fetch and prefetch require their input to describe a valid cycle.
  Input validity: the time must reset on reset clock and must go forwards, but
  it must not move too fast. Furthermore, the cycle-index and
  ref-trigger-offset can only change on when reset clock is true.
   *)
noextract
let trigger_input_valid (cfg: config) (inp: stream trigger_input): stream bool =
  Util.cycle_time_valid cfg inp.reset_ck inp.cycle_time &&
  Util.is_sampled_on #cycle_index inp.cycle_index        inp.reset_ck &&
  Util.is_sampled_on #ref_offset  inp.ref_trigger_offset inp.reset_ck

%splice[] (autolift_binds [`%trigger_input_valid])

(* Assuming the trigger input is valid, the prefetch is valid.
  The prefetch index is the next active trigger after given time; the
  enabled and time-mark triggers contain the corresponding fields.
  *)
noextract
let prefetch_result_valid (cfg: config) (inp: trigger_input) (prefetch: prefetch_result): bool =
  let trigger = trigger_load cfg prefetch.index inp.ref_trigger_offset in
  S32R.v prefetch.index
                     = active_next_after cfg.triggers.trigger_read inp.cycle_index (UInt64.v inp.cycle_time) &&
  prefetch.enabled   = trigger_check_enabled inp.cycle_index trigger &&
  prefetch.time_mark = trigger.time_mark

(* Assuming the trigger input is valid, the fetch is valid: *)
noextract
let fetch_result_valid (cfg: config) (inp: trigger_input) (fetch: fetch_result): bool =
  let trigger = trigger_load cfg fetch.current.index inp.ref_trigger_offset in
  S32R.v fetch.current.index
                          = active_now cfg.triggers.trigger_read inp.cycle_index (UInt64.v inp.cycle_time) &&
  fetch.current.enabled   = trigger_check_enabled inp.cycle_index trigger &&
  fetch.current.time_mark = trigger.time_mark &&
  fetch.trigger_type      = trigger.trigger_type &&
  fetch.message_index     = trigger.message_index

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
  (input: stream trigger_input #_)
    : stream prefetch_result #_ =
  rec' (fun fetch ->
    let pre_index = (S32R.s32r 0 <: trigger_index) `fby` fetch.index in
    let advance = false `fby` (not fetch.enabled || U64.(S32R.s32r_to_u64 fetch.time_mark <= input.cycle_time)) in
    let index =
      if input.reset_ck
      then S32R.s32r 0
      else if advance
      then S32R.inc_sat pre_index
      else pre_index in
    let trigger = trigger_load cfg index input.ref_trigger_offset in
    let enabled = trigger_check_enabled input.cycle_index trigger in
    { index; enabled; time_mark = trigger.time_mark })

%splice[prefetch_core] (autolift_binds [`%prefetch])

let prefetch_rely
  (cfg: config)
  (input: stream trigger_input #_)
    : stream bool #_ =
  trigger_input_valid cfg input

let prefetch_guar
  (cfg: config)
  (pf:    stream prefetch_result)
  (input: stream trigger_input #_)
    : stream bool #_ =
  prefetch_result_valid cfg input pf


%splice[prefetch_rely_core; prefetch_guar_core] (autolift_binds [`%prefetch_rely; `%prefetch_guar])

[@@lifted; of_source(`%prefetch)]
let prefetch_core_contract (cfg: config): S.stream trigger_input -> S.stream prefetch_result =
  let open S in
  let c = Contract.contract_of_stream1 {
    rely = prefetch_rely_core cfg;
    guar = prefetch_guar_core cfg;
    body = prefetch_core      cfg;
  } in
  assert (Contract.system_induct_k1 c) by (T.pipit_simplify_products []; T.dump "OK");
  Contract.stream_of_contract1 c


(*
  Fetch the current trigger, or the next one if there is no current trigger.
*)
[@@Tac.preprocess_with preprocess]
let fetch
  (cfg: config)
  (input: stream trigger_input #_)
    : stream fetch_result #_ =
  let next: stream prefetch_result =
    prefetch cfg input in
  let take_next: stream bool =
    input.reset_ck || (next.enabled && is_started cfg input.cycle_time next.time_mark) in
  let rec current =
    if (true ->^ take_next) then next else pre current in
  let trigger = trigger_load cfg current.index input.ref_trigger_offset in
  { current; trigger_type = trigger.trigger_type; message_index = trigger.message_index; }

%splice[fetch_core] (autolift_binds [`%fetch])



// TODO: move to tx controller;
// this should only reset when reference message cycle = 0
(*^5.1 Tx_Count: each time a Tx_Trigger becomes active, Tx_Count is incremented. Tx_Count is not incremented beyond Expected_Tx_Trigger. *)
(* CLARIFICATION: the definition of "active" is not entirely clear to me.
  Is it whenever a Tx_Trigger trigger array entry is encountered by the trigger loop, or is it only when the trigger is enabled for the current cycle index?
  I think it must be every time it's encountered by the loop, because otherwise we would underflow for a periodic trigger that doesn't transmit every cycle.
  *)
// let tx_counter
//   (reset_ck: stream bool)
//   (prefetch: stream prefetch_result #_)
//     : stream trigger_count #_ =
//   let open S32R in
//   rec' (fun tx_count ->
//     let prev: trigger_count =
//       if reset_ck
//       then s32r 0
//       else s32r 0 `fby` tx_count in
//     let incr =
//       Util.edge #trigger_index prefetch.index &&
//       prefetch.trigger.trigger_type = Tx_Trigger in
//     if incr
//     then inc_sat prev
//     else prev)
// %splice[tx_counter_core] (autolift_binds [`%tx_counter])
