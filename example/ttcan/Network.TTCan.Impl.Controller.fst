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


open Network.TTCan.Types

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module UInt8 = FStar.UInt8
module UInt64= FStar.UInt64
module Cast  = FStar.Int.Cast

(* Result of top-level controller node *)
type controller_result = {
  // Bare minimum fields:
  error:         error_severity;

  driver_enable_acks:
                 bool;

  tx_ref:        Clocked.t ref_message;
  tx_app:        Clocked.t app_message_index;
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


(**** Streaming boilerplate: controller_result stream instance. ****)
instance has_stream_controller_result: S.has_stream controller_result = {
  ty_id       = [`%controller_result];
  val_default = { error = S.val_default; driver_enable_acks = S.val_default; tx_ref = S.val_default; tx_app = S.val_default; tx_delay = S.val_default; } <: controller_result;
}

%splice[controller_result_new] (SugarTac.lift_prim "controller_result_new" (`(fun (error: error_severity) (driver_enable_acks: bool) (tx_ref: Clocked.t ref_message) (tx_app: Clocked.t app_message_index) (tx_delay: ntu) -> { error; driver_enable_acks; tx_ref; tx_app; tx_delay; } <: controller_result)))

instance has_stream_modes_result: S.has_stream modes_result = {
  ty_id       = [`%modes_result];
  val_default = { mode = S.val_default; ref_ck = S.val_default; cycle_index = S.val_default; cycle_time = S.val_default; ref_trigger_offset = S.val_default; sync_state = S.val_default; error_CAN_Bus_Off = S.val_default; error = S.val_default; } <: modes_result
}
%splice[modes_result_new] (SugarTac.lift_prim "modes_result_new" (`(fun (mode: mode) (ref_ck: bool) (cycle_index: cycle_index) (cycle_time: ntu) (ref_trigger_offset: ref_offset) (sync_state: sync_mode) (error_CAN_Bus_Off: bool) (error: error_severity) -> { mode; ref_ck; cycle_index; cycle_time; ref_trigger_offset; sync_state; error_CAN_Bus_Off; error; } <: modes_result)))



// #set-options "--split_queries always"

let modes
  (cfg: config)
  (pre_error:     S.stream error_severity)
  (local_time:    S.stream ntu)
  (mode_cmd:      S.stream (Clocked.t mode))
  (rx_ref:        S.stream (Clocked.t ref_message))
  (pre_tx_ref:    S.stream (Clocked.t ref_message))
  (tx_status:     S.stream tx_status)
  (bus_status:    S.stream bus_status)
    : S.stream modes_result =
  let open S in
  let^ mode        = States.mode_states mode_cmd in

  let^ last_ref    = States.rx_ref_filters rx_ref pre_tx_ref tx_status in
  let^ ref_ck      = Clocked.get_clock last_ref in
  let^ ref_master  = Clocked.map get_master last_ref in
  let^ ref_sof     = Clocked.map get_sof last_ref in
  let^ cycle_index = Clocked.current_or_else (S32R.s32r' 0) (Clocked.map get_cycle_index last_ref) in

  let^ cycle_time  = States.cycle_times mode ref_sof local_time in

  (*^9.3.7 CAN_Bus_Off (S3): the controller went bus-off due to CAN-specific errors *)
  let^ error_CAN_Bus_Off
                   = Util.latch { set = bus_status = const Bus_Off; reset = mode = const Mode_Configure } in
  let^ error       = if_then_else error_CAN_Bus_Off (const S3_Severe) pre_error in

  let^ sync_state  = States.sync_states mode error ref_sof local_time in
  let^ master_state= States.master_modes cfg mode error ref_master in

  let^ ref_trigger_offset
                   = States.ref_trigger_offsets cfg master_state error ref_master in

  modes_result_new mode ref_ck cycle_index cycle_time ref_trigger_offset sync_state error_CAN_Bus_Off error

let trigger_fetch
  (cfg:           config)
  (ref_ck:        S.stream bool)
  (cycle_time:    S.stream ntu)
  (cycle_index:   S.stream cycle_index)
  (ref_trigger_offset:
                  S.stream ref_offset)
    : S.stream Triggers.fetch_result =
  Triggers.fetch cfg ref_ck cycle_time cycle_index ref_trigger_offset


let trigger_tx
  (tx_status:     S.stream tx_status)
  (bus_status:    S.stream bus_status)
  (fetch:         S.stream Triggers.fetch_result)
  (sync_state:    S.stream sync_mode)
  (error:         S.stream error_severity)
    : S.stream (Clocked.t app_message_index & Clocked.t bool) =
  let open S in
  let^ trigger         = Triggers.get_trigger (Triggers.get_current fetch) in
  let^ trigger_enabled = Triggers.get_enabled (Triggers.get_current fetch) in
  let^ trigger_msg     = get_message_index trigger in
  let^ trigger_type    = get_trigger_type  trigger in

  let^ tx_enabled      = (sync_state = const In_Schedule) /\ trigger_enabled /\ (trigger_type = const Tx_Trigger) in

  rec' (fun tx_app_msc_upd ->
    let^ pre_tx_app_ck   = false `fby` Clocked.get_clock (fst tx_app_msc_upd) in

    //^9.2 For messages to be transmitted, the MSC shall be incremented (by one) if the transmission attempt is not successful. The MSC decrement condition shall be different for the error states S0 and S1 and S2.
    let^ tx_success      =
      //^9.2 In S0 and S1, the MSC shall be decremented (by one) when the message has been transmitted successfully.
      if_then_else (Errors.no_error error)
        (tx_status = const Tx_Ok /\ pre_tx_app_ck)
        //^9.2 In S2 (all transmissions are disabled) the MSC shall be decremented by one when the FSE detects bus idle during the Tx_Enable window of the time window for this message.
        (if_then_else (error = const S2_Error)
          (bus_status = const Bus_Idle /\ pre_tx_app_ck)
          (const false))
    in

    let^ tx_pending = rec' (fun tx_pending ->
      if_then_else (Triggers.get_is_new fetch /\ tx_enabled)
        (const true)
        (if_then_else (tx_success \/ (Triggers.get_is_expired fetch))
          (const false)
          (false `fby` tx_pending))) in

    let^ tx_app =
      if_then_else (tx_pending /\ Errors.no_error error)
        (Clocked.some trigger_msg)
        Clocked.none in

    let^ msc_upd =
      if_then_else (Util.falling_edge tx_pending)
        (Clocked.some tx_success)
        Clocked.none in
    tup tx_app msc_upd)


let trigger_rx
  (rx_app:        S.stream (Clocked.t app_message_index))
  (fetch:         S.stream Triggers.fetch_result)
    : S.stream (Clocked.t bool) =
  let open S in
  let^ trigger         = Triggers.get_trigger (Triggers.get_current fetch) in
  let^ trigger_enabled = Triggers.get_enabled (Triggers.get_current fetch) in
  let^ trigger_msg     = get_message_index trigger in
  let^ trigger_type    = get_trigger_type  trigger in

  let^ rx_check        = if_then_else (trigger_enabled /\ trigger_type = const Rx_Trigger /\ Triggers.get_is_expired fetch)
    (Clocked.some trigger_msg)
    Clocked.none in
  let^ rx_check_ok     = MsgSt.rx_pendings rx_check rx_app in

  if_then_else (Clocked.get_clock rx_check)
    (Clocked.some rx_check_ok)
    Clocked.none



let trigger_ref
  (cfg:           config)
  (local_time:    S.stream ntu)
  (tx_status:     S.stream tx_status)
  (bus_status:    S.stream bus_status)
  (cycle_index:   S.stream cycle_index)
  (cycle_time:    S.stream ntu)
  (fetch:         S.stream Triggers.fetch_result)
  (sync_state:    S.stream sync_mode)
  (error:         S.stream error_severity)
    : S.stream (Clocked.t ref_message) =
  let open S in
  let^ trigger         = Triggers.get_trigger (Triggers.get_current fetch) in
  let^ trigger_enabled = Triggers.get_enabled (Triggers.get_current fetch) in
  let^ trigger_type    = get_trigger_type  trigger in

  let^ tx_ref = States.tx_ref_messages cfg local_time sync_state error cycle_time cycle_index
    (trigger_enabled /\ trigger_type = const Tx_Ref_Trigger /\ Triggers.get_is_started fetch) in
  tx_ref



let controller
  (cfg:           config)
  (ref_ck:        S.stream bool)
  (mode:          S.stream mode)
  (cycle_time:    S.stream ntu)
  (fetch:         S.stream Triggers.fetch_result)
  (sync_state:    S.stream sync_mode)
  (error_CAN_Bus_Off:
                  S.stream bool)
  (error:         S.stream error_severity)
  (tx_ref:        S.stream (Clocked.t ref_message))
  (tx_app:        S.stream (Clocked.t app_message_index))
  (tx_msc_upd:    S.stream (Clocked.t bool))
  (rx_msc_upd:    S.stream (Clocked.t bool))
    : S.stream controller_result =
  let open S in
  let^ trigger         = Triggers.get_trigger (Triggers.get_current fetch) in
  let^ trigger_enabled = Triggers.get_enabled (Triggers.get_current fetch) in
  let^ trigger_msg     = get_message_index trigger in
  let^ trigger_type    = get_trigger_type  trigger in

  let^ msc_upd         = Clocked.or_else tx_msc_upd rx_msc_upd in
  let^ msc             = MsgSt.message_status_counters trigger_msg msc_upd in

  let^ tx_delay =
    if_then_else (Triggers.get_is_started fetch)
      (const 0uL)
      U64.(cycle_time - S32R.s32r_to_u64 (get_time_mark trigger)) in

  let^ watch_trigger =
    trigger_type = const Watch_Trigger /\
    trigger_enabled /\
    Triggers.get_is_started fetch in

  // watch trigger: seeing a watch_trigger is only an error if we have previously observed a reference message.
  // entering configure mode resets both error and previously-seen-ref
  let^ error_Watch_Trigger_Reached = Util.latch {
    reset = (mode = const Mode_Configure);
    set   = Util.latch { reset = (mode = const Mode_Configure); set = ref_ck; } /\ watch_trigger
  } in
  // (restart any every (mode = Mode_Configure))(ref_ck) and watch_trigger,
  // mode = Mode_Configure);
//   -- TODO: NOT SUPPORTED YET: Init_Watch_Trigger: requires a different failure mode, doesn't go to S3 as acks must be kept enabled


  let^ error_Tx_Underflow =
    // Check for underflow just before starting new cycle, reset if no underflow upon reaching next cycle
    Errors.cycle_end_check {
      reset = ref_ck;
      set   = sync_state = const In_Schedule /\ S32R.(Triggers.get_tx_count fetch < const cfg.expected_tx_triggers);
    } in

  let^ error_Tx_Overflow =
    // Check for overflow any time, but only reset at new cycle if no overflows
    Errors.transient {
      reset = ref_ck;
      set   = sync_state = const In_Schedule /\ S32R.(Triggers.get_tx_count fetch > const cfg.expected_tx_triggers);
    } in

  // Update MSC min/max-per-cycle whenever we update MSC.
  // should it also update whenever we see a new trigger that we aren't going to update the MSC for?
  let^ error_Scheduling_Error_1 = Errors.scheduling_error_1 ref_ck
  (if_then_else (Clocked.get_clock msc_upd) //  \/ (Triggers.get_is_new fetch /\ ~ trigger_enabled))
    (Clocked.some msc)
    Clocked.none) in

(*^9.3.4 Scheduling_Error_2 (S2) is set if for one transmit message object the MSC has reached 7. It is reset when no transmit object has an MSC of seven. *)
  let^ error_Scheduling_Error_2 = Errors.transient {
    reset = ref_ck;
    set   = Clocked.get_clock tx_msc_upd /\ msc = S32R.s32r 7 /\ trigger_type = const Tx_Trigger;
  } in

  let^ fault_bits = fault_bits_new
    error_Scheduling_Error_1
    error_Tx_Underflow
    error_Scheduling_Error_2
    error_Tx_Overflow
    error_CAN_Bus_Off
    error_Watch_Trigger_Reached in

  let^ error = Errors.summary fault_bits in
  let^ driver_enable_acks = (sync_state <> const Sync_Off) /\ (error <> const S3_Severe) in

  controller_result_new error driver_enable_acks tx_ref tx_app tx_delay


(*



-- (*ERRORS:*)
--   (*^9.3.2 Scheduling_Error_1 (S1) is set if within one matrix cycle the difference between the highest MSC and the lowest MSC of all messages of exclusive time windows of a FSE is larger than 2, or if one of the MSCs of an exclusive receive message object has reached 7.
--     If within one matrix cycle none of these conditions is valid, the bit is reset.
--   *)
--   faultbits_scheduling_error_1_set = latch(trigger = ..., reset = new_basic_cycle)
--   faultbits_scheduling_error_1 = latch(trigger = faultbits_scheduling_error_1_set, reset = new_basic_cycle and not faultbits_scheduling_error_1_set);
--   (*^9.3.4 Scheduling_Error_2 (S2) is set if for one transmit message object the MSC has reached 7. It is reset when no transmit object has an MSC of seven. *)
--   faultbits_scheduling_error_2 = ...;
--   (*^9.3.9 Watch_Trigger_Reached (S3): *)
--   (*^ The S3 error conditions shall remain active until the application updates the configuration. *)
  -- TODO: NOT SUPPORTED YET: Init_Watch_Trigger: requires a different failure mode, doesn't go to S3 as acks must be kept enabled
--   (* Errors not treated: Config_Error (^9.3.8) is statically checked; Application_Watchdog (^9.3.6) is not supported *)

*)
