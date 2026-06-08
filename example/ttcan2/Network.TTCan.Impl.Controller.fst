(** Main TTCan controller. *)
module Network.TTCan.Impl.Controller
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked

module Errors   = Network.TTCan.Impl.Errors
module MsgSt    = Network.TTCan.Impl.MessageStatus
module States   = Network.TTCan.Impl.States
module Triggers = Network.TTCan.Impl.Triggers
module Util     = Network.TTCan.Impl.Util

open Network.TTCan.Types

module UInt8 = FStar.UInt8
module UInt64= FStar.UInt64
module Cast  = FStar.Int.Cast

type driver_input = {
  local_time:  ntu;
  mode_cmd:    Clocked.t mode;
  tx_status:   tx_status;
  bus_status:  bus_status;
  rx_ref:      Clocked.t ref_message;
  rx_app:      Clocked.t trigger_index;
}

(* Result of top-level controller node *)
type controller_result = {
  error:         error_severity;

  driver_enable_acks:
                 bool;

  tx_ref:        Clocked.t ref_message;
  tx_app:        Clocked.t can_buffer_id;
  tx_time_mark:  ntu;
}

type modes_result = {
  mode: mode;
  ref_ck: bool;
  cycle_index: cycle_index;
  cycle_time: ntu;
  ref_trigger_offset: ref_offset;
  sync_state: sync_mode;
  error_CAN_Bus_Off: bool;
  error: error_severity;
}


(**** Streaming boilerplate: struct stream instances ****)
instance has_stream_driver_input: PSSB.has_stream driver_input = {
  ty_id       = [`%driver_input];
  val_default = { local_time = PSSB.val_default; mode_cmd = PSSB.val_default; tx_status = PSSB.val_default; bus_status = PSSB.val_default; rx_ref = PSSB.val_default; rx_app = PSSB.val_default; } <: driver_input;
}

instance has_stream_controller_result: PSSB.has_stream controller_result = {
  ty_id       = [`%controller_result];
  val_default = { error = PSSB.val_default; driver_enable_acks = PSSB.val_default; tx_ref = PSSB.val_default; tx_app = PSSB.val_default; tx_time_mark = PSSB.val_default; } <: controller_result;
}

instance has_stream_modes_result: PSSB.has_stream modes_result = {
  ty_id       = [`%modes_result];
  val_default = { mode = PSSB.val_default; ref_ck = PSSB.val_default; cycle_index = PSSB.val_default; cycle_time = PSSB.val_default; ref_trigger_offset = PSSB.val_default; sync_state = PSSB.val_default; error_CAN_Bus_Off = PSSB.val_default; error = PSSB.val_default; } <: modes_result
}


let modes
  (cfg: config)
  (input:         stream driver_input)
  (pre_error:     stream error_severity)
  (pre_tx_ref:    stream (Clocked.t ref_message))
    : stream modes_result =
  let mode        = States.mode_states input.mode_cmd in

  let last_ref    = States.rx_ref_filters input.rx_ref pre_tx_ref input.tx_status in
  let ref_ck      = Clocked.get_clock last_ref in
  let ref_master  = Clocked.map Mkref_message?.master last_ref in
  let ref_sof     = Clocked.map Mkref_message?.sof last_ref in
  let cycle_index = Clocked.current_or_else (S32R.s32r 0) (Clocked.map Mkref_message?.cycle_index last_ref) in

  let cycle_time  = States.cycle_times mode ref_sof input.local_time in

  (*^9.3.7 CAN_Bus_Off (S3): the controller went bus-off due to CAN-specific errors *)
  let error_CAN_Bus_Off = Util.latch {
    set   = (input.bus_status = Bus_Off);
    reset = (mode = Mode_Configure);
  } in
  let error       = if error_CAN_Bus_Off then S3_Severe else pre_error in

  let sync_state  = States.sync_states mode error ref_sof input.local_time in
  let master_state= States.master_modes cfg mode error ref_master in

  let ref_trigger_offset
                   = States.ref_trigger_offsets cfg master_state error ref_master in

  { mode; ref_ck; cycle_index; cycle_time;
    ref_trigger_offset; sync_state; error_CAN_Bus_Off; error; }

let trigger_fetch
  (cfg:           config)
  (triggers:      stream Triggers.trigger_input)
    : stream Triggers.fetch_result =
  Triggers.fetch cfg triggers

let trigger_tx
  (cfg:           config)
  (tx_status:     stream tx_status)
  (bus_status:    stream bus_status)
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
  (sync_state:    stream sync_mode)
  (error:         stream error_severity)
    : stream (Clocked.t can_buffer_id & Clocked.t bool) =
  let trigger_ix      = fetch.current.index in
  let trigger_enabled = fetch.current.enabled in
  let trigger_msg     = fetch.message_index in
  let trigger_type    = fetch.trigger_type in

  let tx_enabled      = (sync_state = In_Schedule) && trigger_enabled && (trigger_type = Tx_Trigger) in
  let is_expired      = U64.(cycle_time > S32R.s32r_to_u64 fetch.current.time_mark + S32R.s32r_to_u64 cfg.tx_enable_window) in

  let is_new = trigger_ix <> Util.pre #trigger_index trigger_ix in


  rec' (fun tx_app_msc_upd ->
    let pre_tx_app_ck: stream bool =
      false `fby` Clocked.get_clock (fst tx_app_msc_upd) in

    let tx_success      =
      if Errors.no_error error
      then tx_status = Tx_Ok && pre_tx_app_ck
      else if error = S2_Error
      then bus_status = Bus_Idle && pre_tx_app_ck
      else false
    in

    let tx_pending = rec' (fun tx_pending ->
      if is_new && tx_enabled
      then true
      else if tx_success || is_expired
      then false
      else false `fby` tx_pending) in

    let tx_app =
      if tx_pending && Errors.no_error error
      then Some trigger_msg
      else None
    in

    let msc_upd =
      if Util.falling_edge tx_pending
      then Some tx_success
      else None
    in
    (tx_app, msc_upd))

let trigger_rx
  (rx_app:        stream (Clocked.t trigger_index))
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
    : stream (Clocked.t bool) =
  let current         = fetch.current in
  let trigger_enabled = current.enabled in
  let trigger_msg     = fetch.message_index in
  let trigger_type    = fetch.trigger_type in
  let is_expired      = U64.(cycle_time > S32R.s32r_to_u64 current.time_mark) in

  let rx_check        =
    if trigger_enabled && trigger_type = Rx_Trigger && is_expired
    then Some trigger_msg
    else None in
  let rx_check_ok     = MsgSt.rx_pendings rx_check rx_app in

  if Clocked.get_clock rx_check
  then Some rx_check_ok
  else None

let trigger_ref
  (cfg:           config)
  (local_time:    stream ntu)
  (tx_status:     stream tx_status)
  (bus_status:    stream bus_status)
  (cycle_index:   stream cycle_index)
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
  (sync_state:    stream sync_mode)
  (error:         stream error_severity)
    : stream (Clocked.t ref_message) =
  let current         = fetch.current in
  let trigger_enabled = current.enabled in
  let trigger_type    = fetch.trigger_type in
  let is_started      = Triggers.is_started_u64 cycle_time current.time_mark in

  let tx_ref = States.tx_ref_messages cfg local_time sync_state error cycle_time cycle_index
    (trigger_enabled && trigger_type = Tx_Ref_Trigger && is_started) in
  tx_ref

let controller'
  (cfg:           config)
  (input:         stream driver_input)
  (ref_ck:        stream bool)
  (mode:          stream mode)
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
  (sync_state:    stream sync_mode)
  (error_CAN_Bus_Off:
                  stream bool)
  (error:         stream error_severity)
  (tx_ref:        stream (Clocked.t ref_message))
  (tx_app:        stream (Clocked.t can_buffer_id))
  (tx_msc_upd:    stream (Clocked.t bool))
  (rx_msc_upd:    stream (Clocked.t bool))
    : stream controller_result =
  (* PORT BLOCKER: lifting this body verbatim from ttcan fails with an
     Error 19 deep inside the lifter ("Expected type
     Pipit.Context.Base.index_lookup __ctx_controller'_N got type
     Prims.int"). Even minimal stub bodies trigger the same error,
     suggesting an issue with the function's many [stream T] arguments
     and the [controller_result] return record. Workaround: return
     [PSSB.val_default]. *)
  PSSB.val_default

let controller
  (cfg:           config)
  (input:         stream driver_input)
  (ref_ck:        stream bool)
  (mode:          stream mode)
  (cycle_index:   stream cycle_index)
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
  (sync_state:    stream sync_mode)
  (error_CAN_Bus_Off:
                  stream bool)
  (error:         stream error_severity)
    : stream controller_result =
  (* PORT BLOCKER: same lifter Error 19 as [controller'] above
     (Pipit.Context.Base.index_lookup vs Prims.int). Stubbed for
     the same reason. *)
  PSSB.val_default
