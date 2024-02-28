module Network.TTCan.Impl.Controller

module S     = Pipit.Sugar.Shallow
module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked

module Errors   = Network.TTCan.Impl.Errors
module MsgSt    = Network.TTCan.Impl.MessageStatus
module States   = Network.TTCan.Impl.States
module Triggers = Network.TTCan.Impl.Triggers
module Util     = Network.TTCan.Impl.Util

open Pipit.Sugar.Shallow.Tactics.Lift
module Tac = FStar.Tactics


open Network.TTCan.Types

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

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
  // Bare minimum fields:
  error:         error_severity;

  driver_enable_acks:
                 bool;

  tx_ref:        Clocked.t ref_message;
  tx_app:        Clocked.t can_buffer_id;
  tx_delay:      ntu; // note: when tx_ref.ck or tx_app.ck

  // TODO: add other fields:
  // mode:          mode;
  // sync_state:    sync_state;
  // master_state:  master_state;
  // fault_bits:    fault_bits;
  // cycle_time:    ntu;
  // cycle_index:   cycle_index;

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


(**** Streaming boilerplate: struct stream instances and lifting getters/constructors. ****)
instance has_stream_driver_input: S.has_stream driver_input = {
  ty_id       = [`%driver_input];
  val_default = { local_time = S.val_default; mode_cmd = S.val_default; tx_status = S.val_default; bus_status = S.val_default; rx_ref = S.val_default; rx_app = S.val_default; } <: driver_input;
}

instance has_stream_controller_result: S.has_stream controller_result = {
  ty_id       = [`%controller_result];
  val_default = { error = S.val_default; driver_enable_acks = S.val_default; tx_ref = S.val_default; tx_app = S.val_default; tx_delay = S.val_default; } <: controller_result;
}

instance has_stream_modes_result: S.has_stream modes_result = {
  ty_id       = [`%modes_result];
  val_default = { mode = S.val_default; ref_ck = S.val_default; cycle_index = S.val_default; cycle_time = S.val_default; ref_trigger_offset = S.val_default; sync_state = S.val_default; error_CAN_Bus_Off = S.val_default; error = S.val_default; } <: modes_result
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
  let ref_sof     = Clocked.map (fun r -> r.sof) last_ref in
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

%splice[] (autolift_binds [`%modes])

let trigger_fetch
  (cfg:           config)
  (ref_ck:        stream bool)
  (cycle_time:    stream ntu)
  (cycle_index:   stream cycle_index)
  (ref_trigger_offset:
                  stream ref_offset)
    : stream Triggers.fetch_result =
  Triggers.fetch cfg ref_ck cycle_time cycle_index ref_trigger_offset

%splice[] (autolift_binds [`%trigger_fetch])


let trigger_tx
  (cfg:           config)
  (tx_status:     stream tx_status)
  (bus_status:    stream bus_status)
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
  (sync_state:    stream sync_mode)
  (error:         stream error_severity)
    : stream (Clocked.t can_buffer_id & Clocked.t bool) =
  let trigger         = fetch.trigger in
  let trigger_enabled = fetch.current.enabled in
  let trigger_msg     = trigger.message_index in
  let trigger_type    = trigger.trigger_type in

  let tx_enabled      = (sync_state = In_Schedule) && trigger_enabled && (trigger_type = Tx_Trigger) in
  let is_expired      = U64.(cycle_time > S32R.s32r_to_u64 trigger.time_mark + S32R.s32r_to_u64 cfg.tx_enable_window) in

  rec' (fun (tx_app_msc_upd: stream (Clocked.t can_buffer_id & Clocked.t bool)) ->
    let pre_tx_app_ck: stream bool =
      false `fby` Clocked.get_clock (fst tx_app_msc_upd) in

    //^9.2 For messages to be transmitted, the MSC shall be incremented (by one) if the transmission attempt is not successful. The MSC decrement condition shall be different for the error states S0 and S1 and S2.
    let tx_success      =
      //^9.2 In S0 and S1, the MSC shall be decremented (by one) when the message has been transmitted successfully.
      if Errors.no_error error
      then tx_status = Tx_Ok && pre_tx_app_ck
        //^9.2 In S2 (all transmissions are disabled) the MSC shall be decremented by one when the FSE detects bus idle during the Tx_Enable window of the time window for this message.
      else if error = S2_Error
      then bus_status = Bus_Idle && pre_tx_app_ck
      else false
    in

    let tx_pending = rec' (fun tx_pending ->
      if fetch.is_new && tx_enabled
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

%splice[] (autolift_binds [`%trigger_tx])

let trigger_rx
  (rx_app:        stream (Clocked.t trigger_index))
  (cycle_time:    stream ntu)
  (fetch:         stream Triggers.fetch_result)
    : stream (Clocked.t bool) =
  let trigger         = fetch.trigger in
  let trigger_enabled = fetch.current.enabled in
  let trigger_msg     = trigger.message_index in
  let trigger_type    = trigger.trigger_type in
  let is_expired      = U64.(cycle_time > S32R.s32r_to_u64 trigger.time_mark) in

  let rx_check        =
    if trigger_enabled && trigger_type = Rx_Trigger && is_expired
    then Some trigger_msg
    else None in
  let rx_check_ok     = MsgSt.rx_pendings rx_check rx_app in

  if Clocked.get_clock rx_check
  then Some rx_check_ok
  else None

%splice[] (autolift_binds [`%trigger_rx])

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
  let trigger         = fetch.trigger in
  let trigger_enabled = fetch.current.enabled in
  let trigger_type    = trigger.trigger_type in

  let tx_ref = States.tx_ref_messages cfg local_time sync_state error cycle_time cycle_index
    (trigger_enabled && trigger_type = Tx_Ref_Trigger && fetch.is_started) in
  tx_ref

%splice[] (autolift_binds [`%trigger_ref])

let controller'
  (cfg:           config)
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
  let trigger         = fetch.trigger in
  let trigger_enabled = fetch.current.enabled in
  let trigger_msg     = trigger.message_index in
  let trigger_type    = trigger.trigger_type in

  let msc_upd         = Clocked.or_else tx_msc_upd rx_msc_upd in
  let msc             = MsgSt.message_status_counters trigger_msg msc_upd in

  let tx_delay = Triggers.trigger_delay cycle_time fetch in

  let watch_trigger =
    trigger_type = Watch_Trigger &&
    trigger_enabled &&
    fetch.is_started in

  // watch trigger: seeing a watch_trigger is only an error if we have previously observed a reference message.
  // entering configure mode resets both error and previously-seen-ref
  let error_Watch_Trigger_Reached = Util.latch {
    reset = (mode = Mode_Configure);
    set   = Util.latch { reset = (mode = Mode_Configure); set = ref_ck; } && watch_trigger
  } in
  // (restart any every (mode = Mode_Configure))(ref_ck) and watch_trigger,
  // mode = Mode_Configure);
//   -- TODO: NOT SUPPORTED YET: Init_Watch_Trigger: requires a different failure mode, doesn't go to S3 as acks must be kept enabled


  let error_Tx_Underflow =
    // Check for underflow just before starting new cycle, reset if no underflow upon reaching next cycle
    Errors.cycle_end_check {
      reset = ref_ck;
      set   = sync_state = In_Schedule && false // TODO tx_count: S32R.(fetch.tx_count < cfg.expected_tx_triggers);
    } in

  let error_Tx_Overflow =
    // Check for overflow any time, but only reset at new cycle if no overflows
    Errors.transient {
      reset = ref_ck;
      set   = sync_state = In_Schedule && false // TODO tx_count: S32R.(fetch.tx_count > cfg.expected_tx_triggers);
    } in

  // Update MSC min/max-per-cycle whenever we update MSC.
  // should it also update whenever we see a new trigger that we aren't going to update the MSC for?
  let error_Scheduling_Error_1 = Errors.scheduling_error_1 ref_ck
  (if Clocked.get_clock msc_upd //  || (fetch.is_new && not trigger_enabled))
   then Some msc
   else None) in

(*^9.3.4 Scheduling_Error_2 (S2) is set if for one transmit message object the MSC has reached 7. It is reset when no transmit object has an MSC of seven. *)
  let error_Scheduling_Error_2 = Errors.transient {
    reset = ref_ck;
    set   = Clocked.get_clock tx_msc_upd && msc = S32R.s32r 7 && trigger_type = Tx_Trigger;
  } in

  let fault_bits: stream fault_bits = {
    scheduling_error_1 = error_Scheduling_Error_1;
    tx_underflow = error_Tx_Underflow;
    scheduling_error_2 = error_Scheduling_Error_2;
    tx_overflow = error_Tx_Overflow;
    can_bus_off = error_CAN_Bus_Off;
    watch_trigger_reached = error_Watch_Trigger_Reached;
  } in

  let error = Errors.summary fault_bits in
  let driver_enable_acks = (sync_state <> Sync_Off) && (error <> S3_Severe) in

  { error; driver_enable_acks; tx_ref; tx_app; tx_delay; }

%splice[] (autolift_binds [`%controller'])

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
  let tx_ref = trigger_ref cfg input.local_time input.tx_status input.bus_status cycle_index cycle_time fetch sync_state error in
  let rx_msc_upd = trigger_rx input.rx_app cycle_time fetch in
  let tx = trigger_tx cfg input.tx_status input.bus_status cycle_time fetch sync_state error in
  controller' cfg ref_ck mode cycle_time fetch sync_state error_CAN_Bus_Off error tx_ref (fst tx) (snd tx) rx_msc_upd

%splice[] (autolift_binds [`%controller])