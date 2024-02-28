module Network.TTCan.Impl.Errors

module S     = Pipit.Sugar.Shallow
module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked

open Network.TTCan.Types
open Network.TTCan.Impl.Util

module SugarTac  = Pipit.Sugar.Shallow.Tactics

open Pipit.Sugar.Shallow.Tactics.Lift
module Tac = FStar.Tactics

let no_error (error: error_severity): bool =
  error <> S2_Error && error <> S3_Severe

let summary (fault: fault_bits): error_severity =
  if fault.can_bus_off || fault.watch_trigger_reached then S3_Severe
  else if fault.scheduling_error_2 || fault.tx_overflow then S2_Error
  else if fault.scheduling_error_1 || fault.tx_underflow then S1_Warning
  else S0_No_Error

(* Latch for self-correcting errors.
  We set the error flag whenever we see an error (args.set), but we do not
  reset immediately on args.reset. Instead, we wait until we see another reset
  with no error in-between.
  This is used for errors that should only reset once we've seen a completely
  new cycle with no errors in it.
 *)

let transient (args: stream latch_args): stream bool =
  let (* reset at every new cycle (reset) *)
    any_error_this_cycle = latch args
  in
  (* becomes true whenever we see an error; resets when we start a new cycle, and the previous cycle did not have any errors *)
  latch {
    set   = args.set;
    reset = args.reset && not (false `fby` any_error_this_cycle);
  }

%splice[] (autolift_binds [`%transient])

(* Check the error flag at the end of the cycle.
  Some error conditions are only known at the end of a cycle, such as transmit
  trigger underflow. We need to check the error condition just before starting
  the new cycle (denoted by args.reset). *)
let cycle_end_check (args: stream latch_args): stream bool =
  latch {
    set   = args.reset && (false `fby` args.set);
    reset = args.reset;
  }

%splice[] (autolift_binds [`%cycle_end_check])


(*^ 9.1 Scheduling_Error_1:
  > Scheduling_Error_1 (S1) is set if within one matrix cycle the difference between the highest message status count (MSC) and the lowest MSC of all messages (of exclusive time windows) of a FSE is larger than two, or if one of the MSCs of an exclusive receive message object has reached seven.
  If within one matrix cycle none of these conditions is valid, the bit is reset.

  MTTCAN user's manual S4.6:
  > Scheduling_Error_1 (S1)
  >  Sets Error Level TTOST.EL to “01” if within one matrix cycle the difference between the maximum
  >  MSC and the minimum MSC for all trigger memory elements (of exclusive time windows) is larger
  >  than 2, or if one of the MSCs of an exclusive Rx_Trigger has reached 7.
*)
(* CLARIFICATION:
  Here, we incrementally compute the minimum and maximum of each trigger object that we see in
  a cycle as we go, rather than waiting to the end to summarise all of the time-triggered messages. This is subtly different, as we could have multiple transmissions
  for the same message id, but the two transmissions can have different MSC values.
  I believe this online accumulation is the intended behaviour, however, as the above quote from the MTTCAN user's manual refers to "trigger memory elements" rather than "message objects".
  The alternative of checking the MSC array at the beginning of each basic cycle would be more difficult to implement without significantly increasing the worst-case-execution-time.
*)
[@@Tac.preprocess_with preprocess]
let scheduling_error_1 (ref_ck: stream bool) (msc: stream (Clocked.t message_status_counter)): stream bool =
  let open S32R in
  let rng_max: message_status_counter = s32r 7 in
  let rng_min: message_status_counter = s32r 0 in
  let rec minimum =
    let prv = rng_max `fby` minimum in
    let rst = if ref_ck then rng_max else prv in
    min rst (Clocked.get_or_else rng_max msc)
  in
  let rec maximum =
    let prv = rng_min `fby` minimum in
    let rst = if ref_ck then rng_min else prv in
    max rst (Clocked.get_or_else rng_min msc)
  in
  cycle_end_check {
    reset = ref_ck;
    set =
      // DISCREPANCY: according to the spec, the `maximum=7` check should only apply to read triggers, as `Scheduling_Error_2` triggers when any write triggers have `msc=7`.
      // In this implementation, msc=7 will trigger both errors, but Scheduling_Error_2 (S2) will have precedence.
      minimum < dec_sat maximum || maximum = (rng_max <: stream message_status_counter)
  }

%splice[] (autolift_binds [`%scheduling_error_1])
