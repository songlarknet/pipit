(* Extract TTCAN implementation to C code *)
(* NOTE: Extraction currently requires substantial boilerplate; this got worse
  with recent toolchain upgrades. We plan to generate this wrapper code
  automatically soon. *)
module Network.TTCan.Extract

module Types   = Network.TTCan.Types
module Clocked = Network.TTCan.Prim.Clocked
module Ctrl    = Network.TTCan.Impl.Controller
module Triggers= Network.TTCan.Impl.Triggers

module SugarBase = Pipit.Sugar.Base
module XX      = Pipit.Exec.Exp
module XL      = Pipit.Exec.Pulse

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

let tac_extract_full_ttcan () =
  XL.tac_extract_full_strong_generic ["Network.TTCan"] [
    "Network.TTCan.Extract.modes_step";
    "Network.TTCan.Extract.modes_step_apply";
    "Network.TTCan.Extract.trigger_fetch_step";
    "Network.TTCan.Extract.trigger_fetch_step_apply";
    "Network.TTCan.Extract.controller_step";
    "Network.TTCan.Extract.controller_step_apply"
  ] ()

let tac_specialize_ttcan () =
  XL.tac_specialize_strong_generic ["Network.TTCan"] [
    "Network.TTCan.Extract.modes_step";
    "Network.TTCan.Extract.modes_step_apply";
    "Network.TTCan.Extract.trigger_fetch_step";
    "Network.TTCan.Extract.trigger_fetch_step_apply";
    "Network.TTCan.Extract.controller_step";
    "Network.TTCan.Extract.controller_step_apply"
  ] ()

(* Translate the mode controller from stream function to Pipit Core; the
  postprocess partially-evaluates the translation. Mark as noextract as we
  do not want the expression in the generated C code. *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let modes_expr = SugarBase.exp_of_stream3 (Ctrl.modes_core cfg)

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
[@@(Tac.postprocess_with tac_specialize_ttcan)]
let modes_reset = XL.mk_reset_sys modes_system

noextract
inline_for_extraction
let mk_driver_input
  (local_time: Types.ntu)
  (mode_cmd: Clocked.t Types.mode)
  (tx_status: Types.tx_status)
  (bus_status: Types.bus_status)
  (rx_ref: Clocked.t Types.ref_message)
  (rx_app: Clocked.t Types.trigger_index)
  : Ctrl.driver_input
  =
    {
      local_time = local_time;
      mode_cmd = mode_cmd;
      tx_status = tx_status;
      bus_status = bus_status;
      rx_ref = rx_ref;
      rx_app = rx_app;
    }

type modes_input = {
  local_time: Types.ntu;
  mode_cmd: Clocked.t Types.mode;
  tx_status: Types.tx_status;
  bus_status: Types.bus_status;
  rx_ref: Clocked.t Types.ref_message;
  rx_app: Clocked.t Types.trigger_index;
  pre_error: Types.error_severity;
  pre_tx_ref: Clocked.t Types.ref_message;
}

[@@(Tac.postprocess_with tac_extract_full_ttcan)]
noextract
inline_for_extraction
let modes_step_apply
  (inp: modes_input)
  (st: modes_state)
  : (modes_state & Ctrl.modes_result)
  =
    let input = mk_driver_input inp.local_time inp.mode_cmd inp.tx_status inp.bus_status inp.rx_ref inp.rx_app in
    XL.mk_step_pure modes_system (input, (inp.pre_error, (inp.pre_tx_ref, ()))) st

[@@(Tac.postprocess_with tac_specialize_ttcan)]
let modes_step
  (inp: modes_input)
  = XL.mk_step modes_step_apply inp

(* We perform the same steps for the trigger_fetch controller and for the
  top-level controller. We intend to automate this process and remove the
  boilerplate in the future.
*)

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let trigger_fetch_expr = SugarBase.exp_of_stream1 (Ctrl.trigger_fetch_core cfg)

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
type trigger_fetch_state = XX.state_of_exp trigger_fetch_expr

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
inline_for_extraction
let trigger_fetch_system: XX.esystem (Triggers.trigger_input & unit) trigger_fetch_state Triggers.fetch_result =
  assert_norm (XX.extractable trigger_fetch_expr);
  XX.exec_of_exp trigger_fetch_expr


[@@(Tac.postprocess_with tac_specialize_ttcan)]
let trigger_fetch_reset = XL.mk_reset_sys trigger_fetch_system

type trigger_fetch_input = {
  reset_ck: bool;
  cycle_time: Types.ntu_config;
  cycle_index: Types.cycle_index;
  ref_trigger_offset: Types.ref_offset;
}

[@@(Tac.postprocess_with tac_extract_full_ttcan)]
noextract
inline_for_extraction
let trigger_fetch_step_apply
  (inp: trigger_fetch_input)
  (st: trigger_fetch_state)
  : (trigger_fetch_state & Triggers.fetch_result)
  =
    let trigger: Triggers.trigger_input = {
      reset_ck = inp.reset_ck;
      cycle_time = inp.cycle_time;
      cycle_index = inp.cycle_index;
      ref_trigger_offset = inp.ref_trigger_offset;
    } in
    XL.mk_step_pure trigger_fetch_system (trigger, ()) st

[@@(Tac.postprocess_with tac_specialize_ttcan)]
let trigger_fetch_step
  (inp: trigger_fetch_input)
  = XL.mk_step trigger_fetch_step_apply inp


[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
let controller_expr = SugarBase.exp_of_stream9 (Ctrl.controller_core cfg)

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
type controller_state = XX.state_of_exp controller_expr

[@@(Tac.postprocess_with (XL.tac_normalize_pure tac_opt))]
noextract
inline_for_extraction
let controller_system: XX.esystem (Ctrl.driver_input & (bool & (Types.mode & (Types.cycle_index & (Types.ntu & (Triggers.fetch_result & (Types.sync_mode & (bool & (Types.error_severity & unit))))))))) controller_state Ctrl.controller_result =
  assert_norm (XX.extractable controller_expr);
  XX.exec_of_exp controller_expr

[@@(Tac.postprocess_with tac_specialize_ttcan)]
noextract
let controller_reset = XL.mk_reset_sys controller_system

type controller_input = {
  local_time: Types.ntu;
  mode_cmd: Clocked.t Types.mode;
  tx_status: Types.tx_status;
  bus_status: Types.bus_status;
  rx_ref: Clocked.t Types.ref_message;
  rx_app: Clocked.t Types.trigger_index;
  ref_ck: bool;
  mode: Types.mode;
  cycle_index: Types.cycle_index;
  cycle_time: Types.ntu;
  fetch: Triggers.fetch_result;
  sync_state: Types.sync_mode;
  error_CAN_Bus_Off: bool;
  error: Types.error_severity;
}

[@@(Tac.postprocess_with tac_extract_full_ttcan)]
noextract
inline_for_extraction
let controller_step_apply
  (inp: controller_input)
  (st: controller_state)
  : (controller_state & Ctrl.controller_result)
  =
    let input = mk_driver_input inp.local_time inp.mode_cmd inp.tx_status inp.bus_status inp.rx_ref inp.rx_app in
    let packed =
      (input,
       (inp.ref_ck,
        (inp.mode,
         (inp.cycle_index,
          (inp.cycle_time,
           (inp.fetch,
            (inp.sync_state,
             (inp.error_CAN_Bus_Off,
              (inp.error, ()))))))))) in
    XL.mk_step_pure controller_system packed st

[@@(Tac.postprocess_with tac_specialize_ttcan)]
noextract
let controller_step
  (inp: controller_input)
 = XL.mk_step controller_step_apply inp

