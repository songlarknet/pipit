(** State machines (mode, sync, master, ref-trigger-offset, ref-message, cycle-time)

   Port to the new pipeline. See [example/ttcan2/README.md] for the
   active source-level workarounds; the lifter-level bug A
   ([Clocked.t]-arg in [let rec] / [rec'] body) was resolved on
   2026-06-03 in [Pipit.Plugin.Lift.resolve_inst]; bug B (refined-
   return-type instances such as [S32R.s32r 7]) was resolved on
   2026-06-05 in [Pipit.Source.Ast.Reflect.lift_ite] (refinement
   stripping on the if/then/else result type).
*)
module Network.TTCan.Impl.States

module Clocked = Network.TTCan.Prim.Clocked
module S32R    = Network.TTCan.Prim.S32R
module U64     = Network.TTCan.Prim.U64
module Util    = Network.TTCan.Impl.Util

#lang-pipit
open Pipit.Source
(* Open AFTER [Pipit.Source] so [Network.TTCan.Types.Base.mode] shadows
   [Pipit.Plugin.Interface.mode] re-exported by [Pipit.Source]. *)
open Network.TTCan.Types

(* Specialised wrappers around polymorphic Clocked/U64 helpers so the
   lifter sees a monomorphic call site. *)
let goe_ntu (dflt: ntu) (clck: Clocked.t ntu): ntu =
  Clocked.get_or_else dflt clck

let ntu_sub (a b: ntu): ntu = U64.op_Subtraction a b

let cycle_time_capture
  (local_time:         stream ntu)
  (reset_ck:           stream bool)
  (cycle_time_capture: stream (Clocked.t ntu))
    : stream ntu =
  let rec cycle_time_start =
    let dflt =
      if reset_ck
      then local_time
      else 0uL `fby` cycle_time_start
    in
    goe_ntu dflt cycle_time_capture
  in
  ntu_sub local_time cycle_time_start

let cycle_times
  (mode:       stream mode)
  (ref_mark:   stream (Clocked.t ntu))
  (local_time: stream ntu)
    : stream ntu =
  // Reset cycle_time=0 when leaving configure so Sync_Mode.TS1 holds.
  let cycle_time_reset =
    mode = Mode_Configure || Util.pre (mode = Mode_Configure)
  in
  cycle_time_capture local_time cycle_time_reset ref_mark

(* Track the current mode based on mode commands seen so far. *)
let mode_states
  (mode_cmd: stream (Clocked.t mode))
    : stream mode =
  Clocked.current_or_else Mode_Configure mode_cmd

(*^9.4.2 Sync_Mode *)
let sync_states
  (mode:       stream mode)
  (error:      stream error_severity)
  (ref_mark:   stream (Clocked.t ntu))
    : stream sync_mode =
  let rec sync_state =
    let pre_sync = Sync_Off `fby` sync_state in
    let seen_sync_ref_mark = Util.latch {
      set   = Clocked.get_clock ref_mark;
      reset = pre_sync <> Synchronising;
    } in
    (*^9.4.2 transition Sync_Mode.TS0: always taking precedence; HW reset
       or (Mode = Config) or (error state = S3) *)
    if mode = Mode_Configure || error = S3_Severe
    then Sync_Off
    else
      (* Multi-arm match on stream scrutinee unsupported; rewrite as
         if/else chain (README workaround 1). *)
      if pre_sync = Sync_Off then Synchronising
      else if pre_sync = Synchronising then
        (*^9.4.2 transition Sync_Mode.TS3: at least two successive reference
           messages observed *)
        (if Util.pre seen_sync_ref_mark && Clocked.get_clock ref_mark
         then In_Schedule
         else Synchronising)
      else (* pre_sync = In_Schedule *)
        In_Schedule
  in
  sync_state

(*^9.4.3 Master_Mode *)
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
    (*^9.4.3 transition Master_Mode.TM0: always taking precedence;
       HW reset or (Mode = Config) or (error state = S3) *)
    if mode = Mode_Configure || error = S3_Severe
    then Master_Off
    else
      (* Multi-arm match on stream scrutinee unsupported; rewrite the
         [| Master_Off -> ... | _ -> pre_master] match as an if-else
         chain (README workaround 1). *)
      if pre_master = Master_Off then
        (if Clocked.get_clock ref_msg && not master_enable
         then Follower
         else if Clocked.get_clock ref_msg && master_enable && error <> S2_Error
         then (if ref_msg = Some master_index
               then Current_Master
               else Backup_Master)
         else Master_Off)
      else pre_master
  in
  master_mode

(*^9.5.1 Ref_Trigger_Offset *)
let ref_trigger_offsets
  (cfg:         config)
  (master_mode: stream master_mode)
  (error:       stream error_severity)
  (ref_master:  stream (Clocked.t master_index))
    : stream ref_offset =
  let my_master_index = config_master_index cfg in
  let rec ref_trigger_offset =
    let pre_ref = cfg.initial_ref_offset `fby` ref_trigger_offset in
    //^ If [a potential master] becomes current time master (by
    //  successfully transmitting a reference message), it shall use
    //  Ref_Trigger_Offset = 0.
    if master_mode = Current_Master
    then S32R.s32r 0
    //^ [At error level S2,] potential masters may still transmit
    //  reference messages with the Ref_Trigger_Offset set to the
    //  maximum value of 127.
    else if error = S2_Error
    then S32R.s32r 127
    // Downgrading to a backup master
    else if Util.rising_edge (master_mode = Backup_Master)
    then cfg.initial_ref_offset
    // If we start a new basic cycle and the current master is higher
    // index (lower priority) than us, try to reduce our ref offset to
    // overtake the current master.
    else if S32R.op_Greater (Clocked.get_or_else (S32R.s32r 0) ref_master) my_master_index
    then (if S32R.op_Greater pre_ref (S32R.s32r 0)
          then S32R.s32r 0
          else S32R.dec_sat pre_ref)
    else pre_ref
  in
  ref_trigger_offset

(*^9.5.2 Rx_Ref filter: choose the canonical reference message between
   the bus-received [rx_ref] and the previous self-transmitted
   [pre_tx_ref], preferring whichever started earlier. *)
let rx_ref_filters
  (rx_ref:        stream (Clocked.t ref_message))
  (pre_tx_ref:    stream (Clocked.t ref_message))
  (pre_tx_status: stream tx_status)
    : stream (Clocked.t ref_message) =
  let _tx_success = Clocked.get_clock pre_tx_ref && pre_tx_status = Tx_Ok in
  if Clocked.get_clock rx_ref && Clocked.get_clock pre_tx_ref
  then (if U64.op_Less_Equals (Clocked.get_value rx_ref).sof
                              (Clocked.get_value pre_tx_ref).sof
        then rx_ref
        else pre_tx_ref)
  else if Clocked.get_clock rx_ref
  then rx_ref
  else pre_tx_ref

(*^9.1 / ref-message construction: choose when to transmit a reference
   message, applying the severe-error cooldown and clamping the cycle
   index. The output is [Some _] iff this node is allowed and clocked
   to transmit on this tick. *)
let tx_ref_messages
  (cfg:         config)
  (local_time:  stream ntu)
  (sync_state:  stream sync_mode)
  (error:       stream error_severity)
  (cycle_time:  stream ntu)
  (cyc_idx:     stream cycle_index)
  (send_ck:     stream bool)
    : stream (Clocked.t ref_message) =
  let rec severe_error_cooldown =
    if error = S3_Severe
    then U64.op_Plus local_time (S32R.s32r_to_u64 cfg.severe_error_ref_cooldown)
    else (0uL `fby` severe_error_cooldown)
  in
  let cycle_index' =
    if S32R.op_Less cyc_idx cfg.cycle_count_max
    then S32R.inc_sat cyc_idx
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
    U64.op_Less severe_error_cooldown local_time
  in
  //%PROPERTY "^9.1:severe-no-transmission" error = S3_Severe => not tx_ref_ck;
  if tx_ref_ck
  then Some tx_ref
  else None
