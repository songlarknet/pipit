module Network.TTCan.Impl.Errors

module S     = Pipit.Sugar.Shallow
module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R

open Network.TTCan.Types

module SugarTac  = Pipit.Sugar.Shallow.Tactics

let no_error (error: S.stream error_severity): S.stream bool =
  let open S in
  error <> const S2_Error /\ error <> const S3_Severe

// This is a little painful in current Pipit syntax, so write as pure function then lift
let summary' (fault: fault_bits): error_severity =
  if fault.can_bus_off || fault.watch_trigger_reached then S3_Severe
  else if fault.scheduling_error_2 || fault.tx_overflow then S2_Error
  else if fault.scheduling_error_1 || fault.tx_underflow then S1_Warning
  else S0_No_Error

%splice[summary] (SugarTac.lift_prim "summary" (`summary'))

(* Resettable latch.
  Named arguments would be nice, having two boolean args is a bit iffy.
*)
noeq
type latch_args = { set: S.stream bool; reset: S.stream bool }

let latch (args: latch_args): S.stream bool =
  let open S in
  rec' (fun latch ->
    // if_then_else is ugly. maybe a syntax like this would be ok...
    // selects [
    //     When args.set,   const true;
    //     When args.reset, const false;
    //     Otherwise,       false `fby` latch
    //   ]
    if_then_else args.set (const true)
      (if_then_else args.reset (const false) (false `fby` latch)))

(* Latch for self-correcting errors *)
noeq
type transient_args = { ref_ck: S.stream bool; error_cond: S.stream bool }

let transient (args: transient_args): S.stream bool =
  let open S in
  let^
  (* reset at every new cycle (ref_ck) *)
    any_error_this_cycle = latch { set = args.error_cond; reset = args.ref_ck }
  in
  (* becomes true whenever we see an error; resets when we start a new cycle, and the previous cycle did not have any errors *)
  latch {
    set   = args.error_cond;
    reset = args.ref_ck /\ ~ (false `fby` any_error_this_cycle) }

(*


(* Error flag to check just before starting a new cycle. *)
node Error_Cycle_End_Check(
  ref_ck:      bool;
  error_cond:  bool;
) returns (
  error:       bool;
)
let
  error =
    Error_Latch(
      ref_ck and previously(error_cond),
      ref_ck
    );
tel


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
node Error_Scheduling_Error_1(
  ref_ck:      bool;
  msc_ck:      bool;
  msc:         Message_Status_Counter; -- when msc_ck
) returns (
  error:       bool;
)
var
  minimum:     Message_Status_Counter;
  maximum:     Message_Status_Counter;
let
  minimum =
    if ref_ck and msc_ck
    then msc
    else if ref_ck
    then 7
    else if msc_ck and msc < (7 -> pre minimum)
    then msc
    else (7 -> pre minimum);

  maximum =
    if ref_ck and msc_ck
    then msc
    else if ref_ck
    then 0
    else if msc_ck and msc > (0 -> pre maximum)
    then msc
    else (0 -> pre maximum);

  error =
    Error_Cycle_End_Check(
      ref_ck,
      -- DISCREPANCY: according to the spec, the `maximum=7` check should only apply to read triggers, as `Scheduling_Error_2` triggers when any write triggers have `msc=7`.
      -- In this implementation, msc=7 will trigger both errors, but Scheduling_Error_2 (S2) will have precedence.
      minimum < maximum - 1 or maximum = 7
    );
tel
*)