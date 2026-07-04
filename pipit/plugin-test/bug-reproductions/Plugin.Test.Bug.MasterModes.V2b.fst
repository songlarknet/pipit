(* V2b: V2a + the prime suspect: equality test
   [ref_msg = Some master_idx] where the LHS is [stream (option int)]
   and the RHS is a static [option int] lifted to a stream. *)
module Plugin.Test.Bug.MasterModes.V2b
#lang-pipit

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

#set-options "--warn_error -242"

let mm_v2b_opt_eq_int
  (cfg:    config_int)
  (mode_:  stream mode)
  (error:  stream error_severity)
  (ref_msg: stream (option master_index_int))
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
