module Network.TTCan.Types

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base

module U64       = Network.TTCan.Prim.U64

type mode =
  | Mode_Configure | Mode_Running
type mode_cmd =
  | Mode_Cmd_None | Mode_Cmd_Configure | Mode_Cmd_Run

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

// configuration values could be statically limited to 16-bits
// TODO subrange16
type ntu_config = ntu // U16.t

// TODO subrange
type subrange (x: int) (y: int) = U64.t

type ref_offset = subrange (-127) 127
type master_index = subrange 0 7
type cycle_index = subrange 0 63
// power-of-two denoting how often to repeat
type repeat_factor = subrange 0 6

type ref_message = {
  sof:         ntu;
  master:      master_index;
  cycle_index: cycle_index;
  // ref_message_Next_Is_Gap not supported
}

type message_status_counter = subrange 0 7


type trigger = {
  trigger_type:  trigger_type;
  time_mark:     ntu_config;
  cycle_offset:  cycle_index;
  repeat_factor: repeat_factor;
}

type fault_bits = {
  fault_scheduling_error_1:    bool;
  fault_tx_underflow:          bool;
  fault_scheduling_error_2:    bool;
  fault_tx_overflow:           bool;
  fault_can_bus_off:           bool;
  fault_watch_trigger_reached: bool;
}

let init_watch_trigger_time: ntu_config = 65535uL

type config = {
  initial_ref_offset: ref_offset;
  master_index: option master_index;
  tx_enable_window: n: nat { 1 <= n /\ n <= 16 };
  cycle_count_max: cycle_index;

  triggers: list trigger;

  app_message_count: pos;
}


// todo bundle in config
type app_message_index (cfg: config) = subrange 0 (cfg.app_message_count - 1)




// TODO: write a splice tactic to generate this
instance has_stream_mode: Sugar.has_stream mode = {
  ty_id       = [`%mode];
  val_default = Mode_Configure;
}

instance has_stream_mode_cmd: Sugar.has_stream mode_cmd = {
  ty_id       = [`%mode_cmd];
  val_default = Mode_Cmd_None;
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

instance has_stream_trigger: Sugar.has_stream trigger = {
  ty_id       = [`%trigger];
  val_default = { trigger_type = Sugar.val_default; time_mark = Sugar.val_default; cycle_offset = Sugar.val_default; repeat_factor = Sugar.val_default; };
}

instance has_stream_fault_bits: Sugar.has_stream fault_bits = {
  ty_id       = [`%fault_bits];
  val_default = { fault_scheduling_error_1 = false; fault_tx_underflow = false; fault_scheduling_error_2 = false; fault_tx_overflow = false; fault_can_bus_off = false; fault_watch_trigger_reached = false; }
}

