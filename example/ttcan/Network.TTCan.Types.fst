module Network.TTCan.Types

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module U64        = Network.TTCan.Prim.U64
module Subrange   = Network.TTCan.Prim.S32R

module List       = FStar.List.Tot

type mode =
  | Mode_Configure | Mode_Running

type sync_mode =
  | Sync_Off | Synchronising | In_Schedule // not supported: In_Gap
type master_mode =
  | Master_Off | Follower | Current_Master | Backup_Master
type error_severity =
  | S0_No_Error | S1_Warning | S2_Error | S3_Severe

type tx_status =
  | Tx_None | Tx_Ok | Tx_Lost_Arbitration | Tx_Error
type bus_status =
  | Bus_Idle | Bus_Busy | Bus_Bad | Bus_Off

type trigger_type =
  | Tx_Trigger | Rx_Trigger | Tx_Ref_Trigger | Watch_Trigger

(* Network time unit: time in terms of CAN-bitrate clock. The spec specifies a 16-bit local time that overflows regularly, but for now we'll use 64-bit to avoid worrying about overflow. *)
type ntu = U64.t

// configuration values can be statically limited to 16-bits
type ntu_config = Subrange.t { min = 0; max = 65535 } // U16.t

(* @7.4.3 Ref_Trigger_Offset may only take values between -127 [sic] and 127. *)
type ref_offset    = Subrange.t { min = -127; max = 127 }
type master_index  = Subrange.t { min = 0; max = 7 }
type cycle_index   = Subrange.t { min = 0; max = 63 }
// power-of-two denoting how often to repeat
type repeat_factor = Subrange.t { min = 0; max = 6 }

type ref_message = {
  sof:         ntu;
  master:      master_index;
  cycle_index: cycle_index;
  // Next_Is_Gap not supported
}

type message_status_counter = Subrange.t { min = 0; max = 7 }

let max_can_buffer_id = 63
type can_buffer_id = Subrange.t { min = 0; max = max_can_buffer_id }

type trigger = {
  trigger_type:  trigger_type;
  time_mark:     ntu_config;
  cycle_offset:  cycle_index;
  repeat_factor: repeat_factor;
  message_index: can_buffer_id;
}

type fault_bits = {
  scheduling_error_1:    bool;
  tx_underflow:          bool;
  scheduling_error_2:    bool;
  tx_overflow:           bool;
  can_bus_off:           bool;
  watch_trigger_reached: bool;
}

let init_watch_trigger_time: ntu_config = Subrange.s32r 65535

(* The M_TTCAN implementation supports at most 64 triggers, so we apply the same limit. *)
let max_trigger_index = 63
type trigger_index = Subrange.t { min = 0; max = max_trigger_index }
type trigger_count = Subrange.t { min = 0; max = max_trigger_index + 1 }

type tx_enable_window = Subrange.t { min = 1; max = 16 } // spec says upper limit is 16 - why 16?

noeq
type triggers = {
  trigger_index_fun: trigger_index -> trigger;
  trigger_count: (count: trigger_count { Subrange.v count > 0 });
  // TODO: properties like adequate spacing
}

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
  trigger_count: trigger_count;

  ttcan_exec_period: ntu_config;
}

let config_master_enable (cfg: config): bool = Some? cfg.master_index
let config_master_index (cfg: config): master_index =
  match cfg.master_index with
  | None -> Subrange.s32r 0
  | Some ix -> ix

(**** Pipit.Shallow stream instances:
  The following boilerplate is required to embed types in Pipit programs. The
  typeclass instances provide a unique identifier and default value for each
  class. For each record, we also provide a stream-lifted constructor and
  field accessor functions. This is a bit of a pain! We can automate this with
  a tactic later.
*)

(* These subrange instances aren't strictly necessary, but they speed up the typeclass
  inference a fair bit. *)
instance has_stream_ntu_config: Sugar.has_stream ntu_config = Subrange.has_stream_S32R _
instance has_stream_ref_offset: Sugar.has_stream ref_offset = Subrange.has_stream_S32R _
instance has_stream_master_index: Sugar.has_stream master_index = Subrange.has_stream_S32R _
instance has_stream_cycle_index: Sugar.has_stream cycle_index = Subrange.has_stream_S32R _
instance has_stream_repeat_factor: Sugar.has_stream repeat_factor = Subrange.has_stream_S32R _
instance has_stream_message_status_counter: Sugar.has_stream message_status_counter = Subrange.has_stream_S32R _
instance has_stream_can_buffer_id: Sugar.has_stream can_buffer_id = Subrange.has_stream_S32R _
instance has_stream_trigger_index: Sugar.has_stream trigger_index = Subrange.has_stream_S32R _
instance has_stream_trigger_count: Sugar.has_stream trigger_count = Subrange.has_stream_S32R _
instance has_stream_tx_enable_window: Sugar.has_stream tx_enable_window = Subrange.has_stream_S32R _

instance has_stream_mode: Sugar.has_stream mode = {
  ty_id       = [`%mode];
  val_default = Mode_Configure;
}

instance has_stream_sync_mode: Sugar.has_stream sync_mode = {
  ty_id       = [`%sync_mode];
  val_default = Sync_Off;
}

instance has_stream_master_mode: Sugar.has_stream master_mode = {
  ty_id       = [`%master_mode];
  val_default = Master_Off;
}

instance has_stream_error_severity: Sugar.has_stream error_severity = {
  ty_id       = [`%error_severity];
  val_default = S0_No_Error;
}

instance has_stream_tx_status: Sugar.has_stream tx_status = {
  ty_id       = [`%tx_status];
  val_default = Tx_None;
}

instance has_stream_bus_status: Sugar.has_stream bus_status = {
  ty_id       = [`%bus_status];
  val_default = Bus_Idle;
}

instance has_stream_trigger_type: Sugar.has_stream trigger_type = {
  ty_id       = [`%trigger_type];
  val_default = Tx_Trigger;
}

instance has_stream_ref_message: Sugar.has_stream ref_message = {
  ty_id       = [`%ref_message];
  val_default = { sof = Sugar.val_default; master = Sugar.val_default; cycle_index = Sugar.val_default; };
}

%splice[ref_message_new] (SugarTac.lift_prim "ref_message_new" (`(fun sof master cycle_index -> {sof; master; cycle_index })))
%splice[get_sof] (SugarTac.lift_prim "get_sof" (`(fun r -> r.sof)))
%splice[get_master] (SugarTac.lift_prim "get_master" (`(fun r -> r.master)))
%splice[get_cycle_index] (SugarTac.lift_prim "get_cycle_index" (`(fun r -> r.cycle_index)))

instance has_stream_trigger: Sugar.has_stream trigger = {
  ty_id       = [`%trigger];
  val_default = { trigger_type = Sugar.val_default; time_mark = Sugar.val_default; cycle_offset = Sugar.val_default; repeat_factor = Sugar.val_default; message_index = Sugar.val_default; };
}

%splice[trigger_new] (SugarTac.lift_prim "trigger_new" (`(fun trigger_type time_mark cycle_offset repeat_factor message_index -> {trigger_type; time_mark; cycle_offset; repeat_factor; message_index })))
%splice[get_trigger_type] (SugarTac.lift_prim "get_trigger_type" (`(fun r -> r.trigger_type)))
%splice[get_time_mark] (SugarTac.lift_prim "get_time_mark" (`(fun r -> r.time_mark)))
%splice[get_cycle_offset] (SugarTac.lift_prim "get_cycle_offset" (`(fun r -> r.cycle_offset)))
%splice[get_repeat_factor] (SugarTac.lift_prim "get_repeat_factor" (`(fun r -> r.repeat_factor)))
%splice[get_message_index] (SugarTac.lift_prim "get_message_index" (`(fun r -> r.message_index)))

instance has_stream_fault_bits: Sugar.has_stream fault_bits = {
  ty_id       = [`%fault_bits];
  val_default = { scheduling_error_1 = false; tx_underflow = false; scheduling_error_2 = false; tx_overflow = false; can_bus_off = false; watch_trigger_reached = false; }
}

%splice[fault_bits_new] (SugarTac.lift_prim "fault_bits_new" (`(fun scheduling_error_1 tx_underflow scheduling_error_2 tx_overflow can_bus_off watch_trigger_reached -> {scheduling_error_1; tx_underflow; scheduling_error_2; tx_overflow; can_bus_off; watch_trigger_reached })))
// accessors may not be required...
