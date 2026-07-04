(* V0: baseline \u2014 outer-if only, falls through to [pre_master].
   Expected: fast. Establishes the cost of the [let rec _ = ... fby _]
   skeleton plus the two enum equality tests. *)
module Plugin.Test.Bug.MasterModes.V0
#lang-pipit

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

#set-options "--warn_error -242"

let mm_v0_outer_only
  (mode_:  stream mode)
  (error:  stream error_severity)
    : stream master_mode =
  let rec master_mode_ =
    let pre_master = Master_Off `fby` master_mode_ in
    if mode_ = Mode_Configure || error = S3_Severe
    then Master_Off
    else pre_master
  in
  master_mode_
