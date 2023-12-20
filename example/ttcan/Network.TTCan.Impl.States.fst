module Network.TTCan.Impl.States

module S       = Pipit.Sugar.Shallow
module Clocked = Network.TTCan.Prim.Clocked
module S32R    = Network.TTCan.Prim.S32R
module U64     = Network.TTCan.Prim.U64

module Util = Network.TTCan.Impl.Util

open Network.TTCan.Types

let cycle_time_capture
  (local_time: S.stream ntu)
  (reset_ck:           S.stream bool)
  (cycle_time_capture: S.stream (Clocked.t ntu))
    : S.stream ntu =
  let open S in
  let open U64 in
  let^ cycle_time_start = rec' (fun cycle_time_start ->
    let dflt = if_then_else reset_ck
      local_time
      (0uL `fby` cycle_time_start) in
    Clocked.get_or_else dflt cycle_time_capture) in
  let^ cycle_time = local_time - cycle_time_start in
  // check "" (sofar (time_ascending local_time /\ cycle_time_capture <= local_time) ==> cycle_time <= local_time);^
  cycle_time

let cycle_times
  (mode:       S.stream mode)
  (ref_mark:   S.stream (Clocked.t ntu))
  (local_time: S.stream ntu)
    : S.stream ntu =
  let open S in
  // Reset cycle_time=0 when leaving configure to satisfy Sync_Mode.TS1 below; also reset when in configure time to avoid returning an invalid cycle time
  let^ cycle_time_reset = (mode = const Mode_Configure \/ pre (mode = const Mode_Configure)) in
  let^ cycle_time = cycle_time_capture local_time cycle_time_reset ref_mark in
  (*^9.4.2 transition Sync_Mode.TS1: Config_Mode is left, Cycle_Time shall be zero *)
  // --%PROPERTY "^9.4.2 Sync_Mode.TS1: Config_Mode is left, Cycle_Time shall be zero" falling_edge(mode = Mode_Configure) => cycle_time = 0;
  // --%PROPERTY "Sync_Mode.Cycle_Time:ref_mark reset" sync_state = In_Schedule and ref_mark_ck => cycle_time = local_time - ref_mark;
  cycle_time

let mode_states
  (mode_cmd: S.stream (Clocked.t mode))
    : S.stream mode =
  Clocked.current_or_else Mode_Configure mode_cmd

let sync_states
  (mode:       S.stream mode)
  (error:      S.stream error_severity)
  (ref_mark:   S.stream (Clocked.t ntu))
  (local_time: S.stream ntu)
    : S.stream sync_mode =
  let open S in
  (*^9.4.2 Sync_Mode *)
  let sync_state = rec' (fun sync_state ->
    let^ pre_sync = Sync_Off `fby` sync_state in
    let^ seen_sync_ref_mark = Util.latch { set = Clocked.get_clock ref_mark; reset = (pre_sync <> const Synchronising) } in

    (*^9.4.2 transition Sync_Mode.TS0: transition condition always taking prevalance; HW reset or (Mode = Config) or (error state = S3) *)
    if_then_else (mode = const Mode_Configure \/ error = const S3_Severe)
      (const Sync_Off)
      (*^9.4.2 State Sync_Off: No synchronisation activity in progress.. *)
      (if_then_else (pre_sync = const Sync_Off)
      (*^9.4.2 transition Sync_Mode.TS1: Config_Mode is left, Cycle_Time shall be zero *)
        (const Synchronising)
        (*^9.4.2 State Synchronising: FSE is in process of synchronisation but not yet synchronised. *)
        (if_then_else (pre_sync = const Synchronising)
          (*^9.4.2 transition Sync_Mode.TS3: at least two successive reference messages observed (the last reference message did not contain a set Disc_Bit), last reference message did not contain a Next_Is_Gap bit *)
          //^8.2 After reset, a FSE shall consider itself synchronised to the network after the occurrence of the second consecutive reference message
          (if_then_else (pre seen_sync_ref_mark /\ Clocked.get_clock ref_mark)
            (const In_Schedule)
            (*^9.4.2 NOTIMPLEMENTED Next_Is_Gap: transition Sync_Mode.TS2: at least two successive reference messages observed (the last reference message did not contain a set Disc_Bit), last reference message contained a Next_Is_Gap bit *)
            (const Synchronising))
          (if_then_else (pre_sync = const In_Schedule)
            (*^9.4.2 State In_Schedule: FSE is synchronised, no gap expected. *)
            (*^9.4.2 NOTIMPLEMENTED Next_Is_Gap: transition Sync_Mode.TS4: Next_Is_Gap = 1 observed in reference message *)
            (const In_Schedule)
            // IMPOSSIBLE
            (const Sync_Off)))))
  in
  sync_state
  // --%PROPERTY mode = Mode_Configure => sync_state = Sync_Off;
  // --%PROPERTY error = S3_Severe => sync_state = Sync_Off;


let master_modes
  (cfg:     config)
  (mode:    S.stream mode)
  (error:   S.stream error_severity)
  (ref_msg: S.stream (Clocked.t master_index))
    : S.stream master_mode =
  let open S in
  let^ master_enable = const (config_master_enable cfg) in
  let^ master_index  = const (config_master_index cfg) in

  rec' (fun master_mode ->
    let^ pre_master = Master_Off `fby` master_mode in

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
    if_then_else (mode = const Mode_Configure \/ error = const S3_Severe)
      (const Master_Off)
      (if_then_else (pre_master = const Master_Off)
        (if_then_else (Clocked.get_clock ref_msg /\ ~ master_enable)
          (const Follower)
          (if_then_else (Clocked.get_clock ref_msg /\ master_enable /\ error <> const S2_Error)
            (if_then_else (Clocked.get_value ref_msg = master_index)
              (const Current_Master)
              (const Backup_Master))
            (const Master_Off))
        )
        (if_then_else (pre_master = const Backup_Master)
          (if_then_else (error = const S2_Error)
            (const Master_Off)
            (if_then_else S32R.(Clocked.get_clock ref_msg /\ Clocked.get_value ref_msg < master_index)
              (const Backup_Master)
              (const Current_Master)))
          (if_then_else (pre_master = const Follower)
            (const Follower)
            // impossible
            (const Master_Off)))))

let ref_trigger_offsets
  (cfg:         config)
  (master_mode: S.stream master_mode)
  (error:       S.stream error_severity)
  (ref_master:  S.stream (Clocked.t master_index))
    : S.stream ref_offset =
  let open S in
  let open S32R in
  let^ master_index = const (config_master_index cfg) in
  rec' (fun ref_trigger_offset ->
    let^ pre_ref = cfg.initial_ref_offset `fby` ref_trigger_offset in
    //^ If [a potential master] becomes current time master (by successfully transmitting a reference message), it shall use Ref_Trigger_Offset = 0.
    if_then_else (master_mode = const Current_Master)
      (s32r 0)
      //^ [At error level S2,] potential masters may still transmit reference messages with the Ref_Trigger_Offset set to the maximum value of 127.
      (if_then_else (error = const S2_Error)
        (s32r 127)
        // Downgrading to a backup master
        (if_then_else (Util.rising_edge (master_mode = const Backup_Master))
          (const cfg.initial_ref_offset)
          // If we start a new basic cycle and the current master is higher index (lower priority) than us, we want to try to reduce our ref offset to overtake the current master
          (if_then_else (Clocked.get_clock ref_master /\ Clocked.get_value ref_master > master_index)
            (if_then_else (pre_ref > s32r 0)
              (s32r 0)
              (dec_sat pre_ref))
            pre_ref))))


let rx_ref_filters
  (rx_ref:     S.stream (Clocked.t ref_message))
  (pre_tx_ref: S.stream (Clocked.t ref_message))
  (pre_tx_status: S.stream tx_status)
    : S.stream (Clocked.t ref_message) =
  let open S in
  let^ tx_success = Clocked.get_clock pre_tx_ref /\ pre_tx_status = const Tx_Ok in
  let^ last_ref =
    if_then_else (Clocked.get_clock rx_ref /\ Clocked.get_clock pre_tx_ref)
      (if_then_else U64.(get_sof (Clocked.get_value rx_ref) <= get_sof (Clocked.get_value pre_tx_ref))
        rx_ref
        pre_tx_ref)
      (if_then_else (Clocked.get_clock rx_ref)
        rx_ref
        pre_tx_ref) in
  last_ref

let tx_ref_messages
  (cfg:        config)
  (local_time: S.stream ntu)
  (sync_state: S.stream sync_mode)
  (error:      S.stream error_severity)
  (cycle_time: S.stream ntu)
  (cycle_index:S.stream cycle_index)
  (send_ck:    S.stream bool)
    : S.stream (Clocked.t ref_message) =
  let open S in
  let^ severe_error_cooldown = rec' (fun severe_error_cooldown ->
    if_then_else
      (error = const S3_Severe)
      U64.(local_time + S32R.s32r_to_u64 (const cfg.severe_error_ref_cooldown))
      (0uL `fby` severe_error_cooldown)) in

  let^ cycle_index' = S32R.(
        if_then_else S32R.(cycle_index < const cfg.cycle_count_max)
          (inc_sat cycle_index)
          (s32r 0)) in

  let^ tx_ref =
    ref_message_new
      local_time
      (const (config_master_index cfg))
      cycle_index' in

  let^ tx_ref_ck =
    (sync_state = const Synchronising \/ sync_state = const In_Schedule) /\
    send_ck /\
    U64.(severe_error_cooldown < local_time) in

  //%PROPERTY "^9.1:severe-no-transmission" error = S3_Severe => not tx_ref_ck;

  if_then_else tx_ref_ck
    (Clocked.some tx_ref)
    Clocked.none
