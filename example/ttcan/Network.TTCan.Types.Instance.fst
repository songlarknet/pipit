(**** Pipit.Shallow stream instances:
  The following boilerplate is required to embed types in Pipit programs. The
  typeclass instances provide a unique identifier and default value for each
  class. This is a little bit of a pain, but we can automate this with a tactic
  later.
*)
module Network.TTCan.Types.Instance

open Network.TTCan.Types.Base

module Sugar     = Pipit.Sugar.Shallow
module Subrange   = Network.TTCan.Prim.S32R

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

instance has_stream_trigger: Sugar.has_stream trigger = {
  ty_id       = [`%trigger];
  val_default = { trigger_type = Sugar.val_default; time_mark = Sugar.val_default; cycle_offset = Sugar.val_default; repeat_factor = Sugar.val_default; message_index = Sugar.val_default; };
}

instance has_stream_fault_bits: Sugar.has_stream fault_bits = {
  ty_id       = [`%fault_bits];
  val_default = { scheduling_error_1 = false; tx_underflow = false; scheduling_error_2 = false; tx_overflow = false; can_bus_off = false; watch_trigger_reached = false; }
}
