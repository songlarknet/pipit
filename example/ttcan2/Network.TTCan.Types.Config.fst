(* Configuration for a specific TTCan node.
  The config type contains the settings and trigger array, as well as proofs
  that the trigger array can be scheduled.
*)
module Network.TTCan.Types.Config

open Network.TTCan.Types.Base
open Network.TTCan.Types.Triggers

module Subrange   = Network.TTCan.Prim.S32R


noeq
type config = {
  initial_ref_offset: ref_offset;
  master_index: option master_index;
  tx_enable_window: tx_enable_window; // spec says upper limit is 16 - why 16?
  cycle_count_max: cycle_index;


  (*^8.3 When a failed time master reconnects to the system with active time-triggered communication, it shall wait until it is synchronised to the network before attempting to become time master again. *)
  (* This requirement is somewhat vague and seems to introduce a potential deadlock if all masters had previously failed. I have implemented it by specifying a delay to stop transmissions after a severe failure occurs. *)
  severe_error_ref_cooldown: ntu_config;

  triggers: triggers;
  // TODO: trigger validity check: space between them;

  expected_tx_triggers: trigger_count;
}

let config_master_enable (cfg: config): bool = Some? cfg.master_index
let config_master_index (cfg: config): master_index =
  match cfg.master_index with
  | None -> Subrange.s32r 0
  | Some ix -> ix
