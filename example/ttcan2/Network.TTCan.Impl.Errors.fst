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

(*^9.1 Scheduling_Error_1
  TODO: port from [example/ttcan/Network.TTCan.Impl.Errors.fst]. The
  body uses cross-module [S32R.min] / [S32R.max] / [S32R.dec_sat] on
  stream args. Both inlining [S32R.s32r 7] (typeclass resolution fails
  for the refined return type) and lifting [msc_max] / [msc_min] to
  top-level constants (typeclass resolution hangs) have been tried.
  Tracked in [example/ttcan2/README.md] as a higher-priority follow-up. *)
