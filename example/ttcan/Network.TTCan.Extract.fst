(* XXX: broken: extraction causes stack overflow *)
module Network.TTCan.Extract

module Types   = Network.TTCan.Types
module Clocked = Network.TTCan.Prim.Clocked
module Ctrl    = Network.TTCan.Impl.Controller
module Triggers= Network.TTCan.Impl.Triggers

module SugarBase = Pipit.Sugar.Base
module XX      = Pipit.Exec.Exp
module XL      = Pipit.Exec.LowStar

module Tac     = FStar.Tactics

assume val cfg: Types.config

noextract
let tac_opt = ["Network.TTCan"]


[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let modes_expr = SugarBase.exp_of_stream3 (Ctrl.modes cfg)

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
type modes_state = XX.state_of_exp modes_expr

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
inline_for_extraction
let modes_system: XX.esystem (Ctrl.driver_input & (Types.error_severity & (Clocked.t Types.ref_message & unit))) modes_state Ctrl.modes_result =
  assert_norm (XX.extractable modes_expr);
  XX.exec_of_exp modes_expr


[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let modes_reset = XL.mk_reset modes_system

[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let modes_step
  (input:         Ctrl.driver_input)
  (pre_error:     Types.error_severity)
  (pre_tx_ref:    Clocked.t Types.ref_message)
  = XL.mk_step modes_system (input, (pre_error, (pre_tx_ref, ())))



[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let trigger_fetch_expr = SugarBase.exp_of_stream4 (Ctrl.trigger_fetch cfg)

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
type trigger_fetch_state = XX.state_of_exp trigger_fetch_expr

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
inline_for_extraction
let trigger_fetch_system: XX.esystem (bool & (Types.ntu & (Types.cycle_index & (Types.ref_offset & unit)))) trigger_fetch_state Triggers.fetch_result =
  assert_norm (XX.extractable trigger_fetch_expr);
  XX.exec_of_exp trigger_fetch_expr


[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let trigger_fetch_reset = XL.mk_reset trigger_fetch_system

[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let trigger_fetch_step
  (ref_ck:        bool)
  (cycle_time:    Types.ntu)
  (cycle_index:   Types.cycle_index)
  (ref_trigger_offset:
                  Types.ref_offset)
  = XL.mk_step trigger_fetch_system (ref_ck, (cycle_time, (cycle_index, (ref_trigger_offset, ()))))



// [@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
// noextract
// let trigger_tx_expr = SugarBase.exp_of_stream5 Ctrl.trigger_tx

// [@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
// type trigger_tx_state = XX.state_of_exp trigger_tx_expr

// [@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
// noextract
// inline_for_extraction
// let trigger_tx_system: XX.esystem (Types.tx_status & (Types.bus_status & (Triggers.fetch_result & (Types.sync_mode & (Types.error_severity & unit))))) trigger_tx_state (Clocked.t Types.app_message_index & Clocked.t bool) =
//   assert_norm (XX.extractable trigger_tx_expr);
//   XX.exec_of_exp trigger_tx_expr


// [@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
// let trigger_tx_reset = XL.mk_reset trigger_tx_system

// [@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
// let trigger_tx_step
//   (tx_status:     Types.tx_status)
//   (bus_status:    Types.bus_status)
//   (fetch:         Triggers.fetch_result)
//   (sync_state:    Types.sync_mode)
//   (error:         Types.error_severity)
//   = XL.mk_step trigger_tx_system (tx_status, (bus_status, (fetch, (sync_state, (error, ())))))




// [@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
// noextract
// let trigger_rx_expr = SugarBase.exp_of_stream2 Ctrl.trigger_rx

// [@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
// type trigger_rx_state = XX.state_of_exp trigger_rx_expr

// [@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
// noextract
// inline_for_extraction
// let trigger_rx_system: XX.esystem (Clocked.t Types.app_message_index & ((Triggers.fetch_result & unit))) trigger_rx_state (Clocked.t bool) =
//   assert_norm (XX.extractable trigger_rx_expr);
//   XX.exec_of_exp trigger_rx_expr


// [@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
// let trigger_rx_reset = XL.mk_reset trigger_rx_system

// [@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
// let trigger_rx_step
//   (rx_app:        Clocked.t Types.app_message_index)
//   (fetch:         Triggers.fetch_result)
//   = XL.mk_step trigger_rx_system (rx_app, (fetch, ()))


[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let controller_expr = SugarBase.exp_of_stream9 (Ctrl.controller cfg)

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
type controller_state = XX.state_of_exp controller_expr

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
inline_for_extraction
let controller_system: XX.esystem (Ctrl.driver_input & (bool & (Types.mode & (Types.cycle_index & (Types.ntu & (Triggers.fetch_result & (Types.sync_mode & (bool & (Types.error_severity & unit))))))))) controller_state Ctrl.controller_result =
  assert_norm (XX.extractable controller_expr);
  XX.exec_of_exp controller_expr

[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let controller_reset = XL.mk_reset controller_system

[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let controller_step
  (input:         Ctrl.driver_input)
  (ref_ck:        bool)
  (mode:          Types.mode)
  (cycle_index:   Types.cycle_index)
  (cycle_time:    Types.ntu)
  (fetch:         Triggers.fetch_result)
  (sync_state:    Types.sync_mode)
  (error_CAN_Bus_Off:
                  bool)
  (error:         Types.error_severity)
 = XL.mk_step controller_system (input, (ref_ck, (mode, (cycle_index, (cycle_time, (fetch, (sync_state, (error_CAN_Bus_Off, (error, ())))))))))


(*
[@@(Tac.postprocess_with (tac_normalize_pure ["Network.TTCan"]))]
noextract
let expr = SugarBase.exp_of_stream6 (Top.controller cfg)

[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Network.TTCan"]))]
type state = XX.state_of_exp expr

type result = Top.controller_result

[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Network.TTCan"]))]
noextract
inline_for_extraction
let system: XX.esystem (Types.ntu & (Clocked.t Types.mode & (Clocked.t Types.ref_message & (Clocked.t Types.app_message_index & (Types.tx_status & (Types.bus_status & unit)))))) state result =
  assert_norm (XX.extractable expr);
  XX.exec_of_exp expr

[@@(Tac.postprocess_with (XL.tac_extract ["Network.TTCan"]))]
let reset = XL.mk_reset system

[@@(Tac.postprocess_with (XL.tac_extract ["Network.TTCan"]))]
let step
  (local_time: Types.ntu)
  (mode_cmd: Clocked.t Types.mode)
  (rx_ref: Clocked.t Types.ref_message)
  (rx_app: Clocked.t Types.app_message_index)
  (tx_status: Types.tx_status)
  (bus_status: Types.bus_status)
  = XL.mk_step system (local_time, (mode_cmd, (rx_ref, (rx_app, (tx_status, (bus_status, ()))))))
*)



// #push-options "--trace_tactics"
// #push-options "--tactic_trace_d 1"
// #push-options "--debug Network.TTCan.Extract --debug_level NBE"

