(* V2a: adds the [Some?]-on-stream pattern (Clocked-style clock test)
   on top of V1's nested chain. No equality on [option _] streams. *)
module Plugin.Test.Bug.MasterModes.V2a
#lang-pipit

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

#set-options "--warn_error -242"

let mm_v2a_clocked
  (cfg:    config_int)
  (mode_:  stream mode)
  (error:  stream error_severity)
  (ref_msg: stream (option master_index_int))
    : stream master_mode =
  let master_enable = cfg.master_enable in
  let rec master_mode_ =
    let pre_master = Master_Off `fby` master_mode_ in
    if mode_ = Mode_Configure || error = S3_Severe
    then Master_Off
    else
      if pre_master = Master_Off then
        (if Some? ref_msg && not master_enable
         then Follower
         else if Some? ref_msg && master_enable && error <> S2_Error
         then Current_Master
         else Master_Off)
      else pre_master
  in
  master_mode_
