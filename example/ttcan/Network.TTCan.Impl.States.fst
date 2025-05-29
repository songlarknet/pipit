module Network.TTCan.Impl.States

module S       = Pipit.Sugar.Shallow
module Clocked = Network.TTCan.Prim.Clocked
module S32R    = Network.TTCan.Prim.S32R
module U64     = Network.TTCan.Prim.U64

module Util = Network.TTCan.Impl.Util

open Pipit.Sugar.Shallow.Tactics.Lift
open Network.TTCan.Types
module Tac = FStar.Tactics

[@@Tac.preprocess_with preprocess]
let cycle_time_capture
  (local_time:         stream ntu)
  (reset_ck:           stream bool)
  (cycle_time_capture: stream (Clocked.t ntu) #_)
    : stream ntu =
  let open U64 in
  let rec cycle_time_start =
    let dflt = if reset_ck
      then local_time
      else (0uL `fby` cycle_time_start)
    in
    Clocked.get_or_else dflt cycle_time_capture
  in
  let cycle_time = local_time - cycle_time_start in
  // check "" (sofar (time_ascending local_time /\ cycle_time_capture <= local_time) ==> cycle_time <= local_time);^
  cycle_time

%splice[] (autolift_binds [`%cycle_time_capture])


let cycle_times
  (mode:       stream mode)
  (ref_mark:   stream (Clocked.t ntu))
  (local_time: stream ntu)
    : stream ntu =
  // Reset cycle_time=0 when leaving configure to satisfy Sync_Mode.TS1 below; also reset when in configure time to avoid returning an invalid cycle time
  let cycle_time_reset =
    mode = Mode_Configure || pre #bool (mode = Mode_Configure)
  in
  let cycle_time = cycle_time_capture local_time cycle_time_reset ref_mark in
  (*^9.4.2 transition Sync_Mode.TS1: Config_Mode is left, Cycle_Time shall be zero *)
  // --%PROPERTY "^9.4.2 Sync_Mode.TS1: Config_Mode is left, Cycle_Time shall be zero" falling_edge(mode = Mode_Configure) => cycle_time = 0;
  // --%PROPERTY "Sync_Mode.Cycle_Time:ref_mark reset" sync_state = In_Schedule and ref_mark_ck => cycle_time = local_time - ref_mark;
  cycle_time

%splice[] (autolift_binds [`%cycle_times])

let mode_states
  (mode_cmd: stream (Clocked.t mode))
    : stream mode =
  Clocked.current_or_else Mode_Configure mode_cmd

%splice[] (autolift_binds [`%mode_states])

[@@Tac.preprocess_with preprocess]
let sync_states
  (mode:       stream mode)
  (error:      stream error_severity)
  (ref_mark:   stream (Clocked.t ntu))
  (local_time: stream ntu)
    : stream sync_mode =
  (*^9.4.2 Sync_Mode *)
  let rec sync_state =
    let pre_sync = Sync_Off `fby` sync_state in
    let seen_sync_ref_mark = Util.latch {
      set   = Clocked.get_clock ref_mark;
      reset = pre_sync <> Synchronising
    } in
    (*^9.4.2 transition Sync_Mode.TS0: transition condition always taking prevalance; HW reset or (Mode = Config) or (error state = S3) *)
    if mode = Mode_Configure || error = S3_Severe
    then Sync_Off
    else
      match pre_sync with
      (*^9.4.2 State Sync_Off: No synchronisation activity in progress.. *)
      (*^9.4.2 transition Sync_Mode.TS1: Config_Mode is left, Cycle_Time shall be zero *)
      | Sync_Off -> Synchronising
      (*^9.4.2 State Synchronising: FSE is in process of synchronisation but not yet synchronised. *)
      | Synchronising ->
        (*^9.4.2 transition Sync_Mode.TS3: at least two successive reference messages observed (the last reference message did not contain a set Disc_Bit), last reference message did not contain a Next_Is_Gap bit *)
        if pre seen_sync_ref_mark && Clocked.get_clock ref_mark
        //^8.2 After reset, a FSE shall consider itself synchronised to the network after the occurrence of the second consecutive reference message
        then In_Schedule
        (*^9.4.2 NOTIMPLEMENTED Next_Is_Gap: transition Sync_Mode.TS2: at least two successive reference messages observed (the last reference message did not contain a set Disc_Bit), last reference message contained a Next_Is_Gap bit *)
        else Synchronising
      (*^9.4.2 State In_Schedule: FSE is synchronised, no gap expected. *)
      (*^9.4.2 NOTIMPLEMENTED Next_Is_Gap: transition Sync_Mode.TS4: Next_Is_Gap = 1 observed in reference message *)
      | In_Schedule -> In_Schedule
  in
  sync_state
  // --%PROPERTY mode = Mode_Configure => sync_state = Sync_Off;
  // --%PROPERTY error = S3_Severe => sync_state = Sync_Off;

%splice[] (autolift_binds [`%sync_states])

[@@Tac.preprocess_with preprocess]
let master_modes
  (cfg:     config)
  (mode:    stream mode)
  (error:   stream error_severity)
  (ref_msg: stream (Clocked.t master_index))
    : stream master_mode =
  let master_enable = config_master_enable cfg in
  let master_index  = config_master_index cfg in

  let rec master_mode =
    let pre_master = Master_Off `fby` master_mode in

    // --%PROPERTY "Master_Mode.Master_Off.enabled-on-message" ref_msg_ck and mode <> Mode_Configure and error <> S2_Error and error <> S3_Severe => master_mode <> Master_Off;
    // --%PROPERTY "Master_Mode.master-not-follower" config_master_enable => master_mode <> Follower;
    // --%PROPERTY "Master_Mode.follower-not-master" not config_master_enable => master_mode = Master_Off or master_mode = Follower;
    // --%PROPERTY "Master_Mode.error-S2" error = S2_Error => master_mode = Master_Off or master_mode = Follower;

    (*^9.4.3 transition Master_Mode.TM0: transition condition always taking prevalence; HW reset or (Mode = Config) or (error state = S3) *)
    // --%PROPERTY "^9.4.3 Master_Mode.TM0.1(reset)" (true -> false) and not ref_msg_ck => master_mode = Master_Off;
    // --%PROPERTY "^9.4.3 Master_Mode.TM0.2" mode = Mode_Configure or error = S3_Severe => master_mode = Master_Off;

    (*^9.4.3 transition Master_Mode.TM1 (from Master_Off): FSE is not potential master and a reference message is observed *)
    // --%PROPERTY "^9.4.3 Master_Mode.TM1" mode <> Mode_Configure and No_Error(error) and not config_master_enable and ref_msg_ck => master_mode = Follower;

    (*^9.4.3 transition Master_Mode.TM2 (from Master_Off): FSE is potential master, error state is not S2 or S3, reference message is observed from other master *)
    (*^9.4.3 transition Master_Mode.TM3 (from Master_Off): FSE is potential master, error state is not S2 or S3, reference message is observed from self *)

    (*^9.4.3 transition Master_Mode.TM4 (from Backup_Master): FSE changes from backup master to current master when it observes a reference message with its own time master priority *)
    (*^9.4.3 transition Master_Mode.TM6 (from Backup_Master): error state = S2 *)

    (*^9.4.3 transition Master_Mode.TM5 (from Current_Master): FSE changes from current master to backup master when it observes a reference message with a time master priority higher than its own *)
    (*^9.4.3 transition Master_Mode.TM7 (from Current_Master): error state = S2 *)

    (*^9.4.3 transition Master_Mode.TM0: transition condition always taking prevalence; HW reset or (Mode = Config) or (error state = S3) *)
    if mode = Mode_Configure || error = S3_Severe
    then Master_Off
    else match pre_master with
         | Master_Off ->
            if Clocked.get_clock ref_msg && not master_enable
            then Follower
            else if Clocked.get_clock ref_msg && master_enable && error <> S2_Error
            then (if ref_msg = Some master_index
                  then Current_Master
                  else Backup_Master)
            else Master_Off
        | _ -> pre_master

  in master_mode

%splice[] (autolift_binds [`%master_modes])

[@@Tac.preprocess_with preprocess]
let ref_trigger_offsets
  (cfg:         config)
  (master_mode: stream master_mode)
  (error:       stream error_severity)
  (ref_master:  stream (Clocked.t master_index))
    : stream ref_offset =
  let open S32R in
  let master_index = config_master_index cfg in
  let rec ref_trigger_offset: stream ref_offset =
    let pre_ref: stream ref_offset = cfg.initial_ref_offset `fby` ref_trigger_offset in
    //^ If [a potential master] becomes current time master (by successfully transmitting a reference message), it shall use Ref_Trigger_Offset = 0.
    if master_mode = Current_Master
    then s32r 0
    //^ [At error level S2,] potential masters may still transmit reference messages with the Ref_Trigger_Offset set to the maximum value of 127.
    else if error = S2_Error
    then s32r 127
    // Downgrading to a backup master
    else if Util.rising_edge (master_mode = Backup_Master)
    then cfg.initial_ref_offset
    // If we start a new basic cycle and the current master is higher index (lower priority) than us, we want to try to reduce our ref offset to overtake the current master
    else if Clocked.get_or_else (s32r 0) ref_master  > master_index
    then (if S32R.(pre_ref > s32r 0)
          then s32r 0
          else dec_sat pre_ref)
    else pre_ref
  in ref_trigger_offset

%splice[] (autolift_binds [`%ref_trigger_offsets])

[@@Tac.preprocess_with preprocess]
let rx_ref_filters
  (rx_ref:     stream (Clocked.t ref_message))
  (pre_tx_ref: stream (Clocked.t ref_message))
  (pre_tx_status: stream tx_status)
    : stream (Clocked.t ref_message) =
  let tx_success = Clocked.get_clock pre_tx_ref && pre_tx_status = Tx_Ok in
  let last_ref =
    if Clocked.get_clock rx_ref && Clocked.get_clock pre_tx_ref
    then (if U64.((Clocked.get_value rx_ref).sof <= (Clocked.get_value pre_tx_ref).sof)
          then rx_ref
          else pre_tx_ref)
    else if Clocked.get_clock rx_ref
    then rx_ref
    else pre_tx_ref
  in last_ref

%splice[] (autolift_binds [`%rx_ref_filters])

[@@Tac.preprocess_with preprocess]
let tx_ref_messages
  (cfg:        config)
  (local_time: stream ntu)
  (sync_state: stream sync_mode)
  (error:      stream error_severity)
  (cycle_time: stream ntu)
  (cycle_index:stream cycle_index)
  (send_ck:    stream bool)
    : stream (Clocked.t ref_message) =
  let rec severe_error_cooldown =
    if error = S3_Severe
    then U64.(local_time + S32R.s32r_to_u64 cfg.severe_error_ref_cooldown)
    else (0uL `fby` severe_error_cooldown)
  in
  let cycle_index' =
    if S32R.(cycle_index < cfg.cycle_count_max)
    then S32R.inc_sat cycle_index
    else S32R.s32r 0
  in
  let tx_ref: stream ref_message = {
    sof         = local_time;
    master      = config_master_index cfg;
    cycle_index = cycle_index';
  } in
  let tx_ref_ck =
    (sync_state = Synchronising || sync_state = In_Schedule) &&
    send_ck &&
    U64.(severe_error_cooldown < local_time)
  in

  //%PROPERTY "^9.1:severe-no-transmission" error = S3_Severe => not tx_ref_ck;
  if tx_ref_ck
  then Some tx_ref
  else None

%splice[] (autolift_binds [`%tx_ref_messages])
