module Network.TTCan.Impl.Errors
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked

module Prim  = PipitRuntime.Prim

open Network.TTCan.Types
open Network.TTCan.Impl.Util

let no_error (error: error_severity): bool =
  error <> S2_Error && error <> S3_Severe

let summary (fault: fault_bits): error_severity =
  if fault.can_bus_off || fault.watch_trigger_reached then S3_Severe
  else if fault.scheduling_error_2 || fault.tx_overflow then S2_Error
  else if fault.scheduling_error_1 || fault.tx_underflow then S1_Warning
  else S0_No_Error

let transient (args: stream latch_args): stream bool =
  let any_error_this_cycle = latch args in
  latch {
    set   = args.set;
    reset = args.reset && not (pre any_error_this_cycle);
  }

let cycle_end_check (args: stream latch_args): stream bool =
  latch {
    set   = args.reset && pre args.set;
    reset = args.reset;
  }

(*^ 9.1 Scheduling_Error_1:
  > Scheduling_Error_1 (S1) is set if within one matrix cycle the difference between the highest message status count (MSC) and the lowest MSC of all messages (of exclusive time windows) of a FSE is larger than two, or if one of the MSCs of an exclusive receive message object has reached seven.
  If within one matrix cycle none of these conditions is valid, the bit is reset.
*)
let scheduling_error_1 (ref_ck: stream bool) (msc: stream (Clocked.t message_status_counter)): stream bool =
  let rec minimum =
    let prv = (S32R.s32r 7 <: message_status_counter) `fby` minimum in
    let rst = if ref_ck then (S32R.s32r 7 <: message_status_counter) else prv in
    S32R.min rst (Clocked.get_or_else (S32R.s32r 7 <: message_status_counter) msc)
  in
  let rec maximum =
    let prv = (S32R.s32r 0 <: message_status_counter) `fby` minimum in
    let rst = if ref_ck then (S32R.s32r 0 <: message_status_counter) else prv in
    S32R.max rst (Clocked.get_or_else (S32R.s32r 0 <: message_status_counter) msc)
  in
  cycle_end_check {
    reset = ref_ck;
    set =
      // DISCREPANCY: according to the spec, the `maximum=7` check should only apply to read triggers, as `Scheduling_Error_2` triggers when any write triggers have `msc=7`.
      // In this implementation, msc=7 will trigger both errors, but Scheduling_Error_2 (S2) will have precedence.
      S32R.lt minimum (S32R.dec_sat maximum) || maximum = (S32R.s32r 7 <: message_status_counter)
  }
