(* Base type definitions *)
module Network.TTCan.Types.Base

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
type ntu_config_pos = Subrange.t { min = 1; max = 65535 }

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
let max_trigger_count = max_trigger_index + 1
type trigger_index = Subrange.t { min = 0; max = max_trigger_index }
type trigger_count = Subrange.t { min = 0; max = max_trigger_count }

type tx_enable_window = Subrange.t { min = 1; max = 16 } // spec says upper limit is 16 - why 16?
