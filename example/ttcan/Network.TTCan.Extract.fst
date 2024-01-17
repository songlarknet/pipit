(* Extract TTCAN implementation to C code *)
module Network.TTCan.Extract

module Types   = Network.TTCan.Types
module Clocked = Network.TTCan.Prim.Clocked
module Ctrl    = Network.TTCan.Impl.Controller
module Triggers= Network.TTCan.Impl.Triggers

module SugarBase = Pipit.Sugar.Base
module XX      = Pipit.Exec.Exp
module XL      = Pipit.Exec.LowStar

module Tac     = FStar.Tactics

(* The configuration defines the actual triggers array; we assume it is
  implemented in C. We declare the configuration as const so the C compiler
  can inline the concrete configuration.
*)
[@@CPrologue "const"]
assume val cfg: Types.config

(* The Pipit normalise tactics take a set of modules to inline. We tell it to
  inline everything in Network.TTCan: *)
noextract
let tac_opt = ["Network.TTCan"]

(* Translate the mode controller from stream function to Pipit Core; the
  postprocess partially-evaluates the translation. Mark as noextract as we
  do not want the expression in the generated C code. *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let modes_expr = SugarBase.exp_of_stream3 (Ctrl.modes cfg)

(* Define the state type for mode controller *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
type modes_state = XX.state_of_exp modes_expr

(* Translate the Pipit Core to an executable system *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
inline_for_extraction
let modes_system: XX.esystem (Ctrl.driver_input & (Types.error_severity & (Clocked.t Types.ref_message & unit))) modes_state Ctrl.modes_result =
  assert_norm (XX.extractable modes_expr);
  XX.exec_of_exp modes_expr

(* Finally, generate the reset and step functions for the mode controller *)
[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let modes_reset = XL.mk_reset modes_system
[@@(Tac.postprocess_with (XL.tac_extract tac_opt))]
let modes_step
  (input:         Ctrl.driver_input)
  (pre_error:     Types.error_severity)
  (pre_tx_ref:    Clocked.t Types.ref_message)
  = XL.mk_step modes_system (input, (pre_error, (pre_tx_ref, ())))

(* We perform the same steps for the trigger_fetch controller and for the
  top-level controller. We intend to automate this process and remove the
  boilerplate in the future.
*)

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

