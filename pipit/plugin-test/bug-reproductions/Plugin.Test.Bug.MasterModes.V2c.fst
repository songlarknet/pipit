(* V2c: identical to V2b but [master_index] is the refined
   [{ 0 <= _ <= 7 }] type, matching the real codebase. If V2b is fast
   and V2c is slow, the cost is in the refinement-encoded equality. *)
module Plugin.Test.Bug.MasterModes.V2c
#lang-pipit

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

#set-options "--warn_error -242"

let mm_v2c_opt_eq_refined
  (cfg:    config_sr)
  (mode_:  stream mode)
  (error:  stream error_severity)
  (ref_msg: stream (option master_index_sr))
    : stream master_mode =
  let master_enable = cfg.master_enable in
  let master_idx    = cfg.master_idx    in
  let rec master_mode_ =
    let pre_master = Master_Off `fby` master_mode_ in
    if mode_ = Mode_Configure || error = S3_Severe
    then Master_Off
    else
      if pre_master = Master_Off then
        (if Some? ref_msg && not master_enable
         then Follower
         else if Some? ref_msg && master_enable && error <> S2_Error
         then (if ref_msg = Some master_idx
               then Current_Master
               else Backup_Master)
         else Master_Off)
      else pre_master
  in
  master_mode_
