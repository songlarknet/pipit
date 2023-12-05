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


(**** Streaming boilerplate: controller_result stream instance. ****)
instance has_stream_controller_result: S.has_stream controller_result = {
  ty_id       = [`%controller_result];
  val_default = { error = S.val_default; driver_enable_acks = S.val_default; tx_ref = S.val_default; tx_app = S.val_default; tx_delay = S.val_default; };
}

%splice[controller_result_new] (SugarTac.lift_prim "controller_result_new" (`(fun (error: error_severity) (driver_enable_acks: bool) (tx_ref: Clocked.t ref_message) (tx_app: Clocked.t app_message_index) (tx_delay: ntu) -> { error; driver_enable_acks; tx_ref; tx_app; tx_delay; })))
%splice[get_error] (SugarTac.lift_prim "get_error" (`(fun c -> c.error)))
%splice[get_tx_ref] (SugarTac.lift_prim "get_tx_ref" (`(fun c -> c.tx_ref)))
%splice[get_tx_app] (SugarTac.lift_prim "get_tx_app" (`(fun c -> c.tx_app)))
%splice[get_tx_delay] (SugarTac.lift_prim "get_tx_delay" (`(fun c -> c.tx_delay)))

#set-options "--split_queries always"

let controller
  (cfg: config)
  (local_time:    S.stream ntu)
  (mode_cmd:      S.stream (Clocked.t mode))
  (rx_ref:        S.stream (Clocked.t ref_message))
  (rx_app:        S.stream (Clocked.t app_message_index))
  (tx_status:     S.stream tx_status)
  (bus_status:    S.stream bus_status)
    : S.stream controller_result =
  let open S in
  rec' (fun ctrl ->
    let^ mode = States.mode_states mode_cmd in

    let^ pre_tx_ref = Clocked.none' `fby` get_tx_ref ctrl in
    let^ last_ref = States.rx_ref_filters rx_ref pre_tx_ref tx_status in

    let^ ref_ck = Clocked.get_clock last_ref in
    let^ ref_master = Clocked.map get_master last_ref in
    let^ cycle_index = Clocked.current_or_else (S32R.s32r' 0) (Clocked.map get_cycle_index last_ref) in

    (*^9.3.7 CAN_Bus_Off (S3): the controller went bus-off due to CAN-specific errors *)
    let^ error_CAN_Bus_Off = Util.latch { set = bus_status = const Bus_Off; reset = mode = const Mode_Configure } in

    let^ init_error =
    if_then_else error_CAN_Bus_Off (const S3_Severe)
    (S0_No_Error `fby` get_error ctrl) in

    let^ sync_statex = States.sync_states mode init_error (Clocked.map get_sof last_ref) local_time in
    let^ sync_state = fst sync_statex in
    let^ cycle_time = snd sync_statex in

    let^ master_state = States.master_modes cfg mode init_error ref_master in

    let^ ref_trigger_offset = States.ref_trigger_offsets cfg master_state init_error ref_master in



    let^ fetch = Triggers.fetch cfg (Clocked.get_clock last_ref) cycle_time cycle_index ref_trigger_offset in
    let^ trigger = Triggers.get_trigger (Triggers.get_current fetch) in
    let^ trigger_msg = get_message_index trigger in
    let^ trigger_enabled = Triggers.get_enabled (Triggers.get_current fetch) in

  // (trigger_new, trigger_enabled, trigger, trigger_started, trigger_expired, tx_count) = Trigger_Fetch(ref_ck, cycle_time, cycle_index, ref_trigger_offset);

    let^ rx_check_ck = trigger_enabled /\ get_trigger_type trigger = const Rx_Trigger /\ Triggers.get_is_expired fetch in
    let^ rx_check = if_then_else rx_check_ck (Clocked.some trigger_msg) Clocked.none in
    let^ rx_check_ok = MsgSt.rx_pendings rx_check rx_app in

    let^ tx_enabled = (sync_state = const In_Schedule) /\ trigger_enabled /\ (get_trigger_type trigger = const Tx_Trigger) in

    let^ pre_tx_app_ck = false `fby` Clocked.get_clock (get_tx_app ctrl) in

    //^9.2 For messages to be transmitted, the MSC shall be incremented (by one) if the transmission attempt is not successful. The MSC decrement condition shall be different for the error states S0 and S1 and S2.
    let^ tx_success =
      //^9.2 In S0 and S1, the MSC shall be decremented (by one) when the message has been transmitted successfully.
      if_then_else (Errors.no_error init_error /\ tx_status = const Tx_Ok /\ pre_tx_app_ck)
        (const true)
        //^9.2 In S2 (all transmissions are disabled) the MSC shall be decremented by one when the FSE detects bus idle during the Tx_Enable window of the time window for this message.
        (if_then_else (init_error = const S2_Error /\ bus_status = const Bus_Idle /\ pre_tx_app_ck)
          (const true)
          (const false))
    in

    let^ tx_pending = rec' (fun tx_pending ->
      if_then_else (Triggers.get_is_new fetch /\ tx_enabled)
        (const true)
        (if_then_else (tx_success \/ (Triggers.get_is_expired fetch))
          (const false)
          (false `fby` tx_pending))) in

    let^ tx_app =
      if_then_else (tx_pending /\ Errors.no_error init_error)
        (Clocked.some trigger_msg)
        Clocked.none in

    let^ msc_ck = rx_check_ck \/ (false `fby` tx_pending) in
    let^ msc_ok =
      if_then_else msc_ck
        (if_then_else (get_trigger_type trigger = const Rx_Trigger)
          (Clocked.some (rx_check_ok /\ bus_status <> const Bus_Bad))
          (if_then_else (get_trigger_type trigger = const Tx_Trigger /\ Util.falling_edge(tx_pending))
            (Clocked.some tx_success)
            (Clocked.some (const false))))
        Clocked.none in

    let^ msc = MsgSt.message_status_counters trigger_msg msc_ok in

    let^ tx_ref = States.tx_ref_messages cfg local_time sync_state init_error cycle_time cycle_index
      (trigger_enabled /\ get_trigger_type trigger = const Tx_Ref_Trigger /\ Triggers.get_is_started fetch) in

    let^ tx_delay =
      if_then_else (Triggers.get_is_started fetch)
        (const 0uL)
        U64.(cycle_time - S32R.s32r_to_u64 (get_time_mark trigger)) in

    let^ watch_trigger =
      get_trigger_type trigger = const Watch_Trigger /\
      trigger_enabled /\ Triggers.get_is_started fetch in

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

    // Update MSC min/max-per-cycle whenever we update MSC, as well as whenever we see a new trigger that we aren't going to update the MSC for.
    let^ error_Scheduling_Error_1 = Errors.scheduling_error_1 ref_ck
    (if_then_else (msc_ck \/ (Triggers.get_is_new fetch /\ ~ trigger_enabled))
      (Clocked.some msc)
      Clocked.none) in

  (*^9.3.4 Scheduling_Error_2 (S2) is set if for one transmit message object the MSC has reached 7. It is reset when no transmit object has an MSC of seven. *)
    let^ error_Scheduling_Error_2 = Errors.transient {
      reset = ref_ck;
      set   = msc_ck /\ msc = S32R.s32r 7 /\ get_trigger_type trigger = const Tx_Trigger;
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
  )


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
