(* XXX: broken: extraction causes stack overflow *)
module Network.TTCan.Extract

module Types   = Network.TTCan.Types
module Clocked = Network.TTCan.Prim.Clocked
module Top = Network.TTCan.Impl.Controller

module SugarBase = Pipit.Sugar.Base
module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.LowStar

module Tac = FStar.Tactics

assume val cfg: Types.config

let norm_delta_options (namespaces: list string) = [delta_namespace ("Pipit" :: "FStar" :: namespaces); nbe; zeta; iota; primops]

(* Re-exports *)
let norm_full (namespaces: list string) =
  Tac.norm (norm_delta_options namespaces)

let tac_normalize_pure (namespaces: list string) () =
  // Do not unfold PipitRuntime here.
  // Tac.norm [delta_namespace ["Network.TTCan"; "Pipit"; "FStar"]; zeta; iota; primops];
  Tac.norm [delta_namespace ["Network.TTCan"]; nbe; zeta; iota; primops];
  Tac.dump "n1";
  Tac.norm [delta_namespace ["FStar"]; nbe; zeta; iota; primops];
  Tac.dump "n2";
  Tac.norm [delta_namespace ["Pipit.Sugar"]; nbe; zeta; iota; primops];
  Tac.dump "n3";
  Tac.norm [delta_namespace ["Pipit"]; nbe; zeta; iota; primops];
  Tac.dump "n4";
  norm_full namespaces;
  Tac.dump "nX";
  Tac.trefl ()

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