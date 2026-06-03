(** State machines (mode, sync, master, ref-trigger-offset, ref-message, cycle-time)

   Port to the new pipeline. See [example/ttcan2/README.md] for the
   active source-level workarounds; the lifter-level bug A
   ([Clocked.t]-arg in [let rec] / [rec'] body) was resolved on
   2026-06-03 in [Pipit.Plugin.Lift.resolve_inst]. Bug B (refined-
   return-type instances such as [S32R.s32r 7]) is still tracked.
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
