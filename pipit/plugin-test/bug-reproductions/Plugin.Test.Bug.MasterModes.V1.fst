(* V1: full nested if/else chain, no [option]/[Clocked] anywhere.
   Same skeleton as [States.master_modes] but with a plain [bool]
   [ref_ck] standing in for [Clocked.get_clock ref_msg]. *)
module Plugin.Test.Bug.MasterModes.V1
#lang-pipit

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

#set-options "--warn_error -242"

let mm_v1_nested
  (cfg:    config_int)
  (mode_:  stream mode)
  (error:  stream error_severity)
  (ref_ck: stream bool)
    : stream master_mode =
  let master_enable = cfg.master_enable in
  let rec master_mode_ =
    let pre_master = Master_Off `fby` master_mode_ in
    if mode_ = Mode_Configure || error = S3_Severe
    then Master_Off
    else
      if pre_master = Master_Off then
        (if ref_ck && not master_enable
         then Follower
         else if ref_ck && master_enable && error <> S2_Error
         then Current_Master
         else Master_Off)
      else pre_master
  in
  master_mode_
