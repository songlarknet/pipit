module Plugin.Test.Example.Pump.Check
#lang-pipit

(* A port of example/Pump.Check.fst using the #lang-pipit preprocessor.

  Each helper is a plain stream function; the [@@proof_induct1] attribute
  asks the plugin to synthesise a __check_<id> binding that discharges all
  embedded [check]s by 1-induction (norm_full []). *)

open Pipit.Source
module PSSB = Pipit.Sugar.Shallow.Base

(* --- Helpers --------------------------------------------------------- *)

let min (a b: stream int): stream int =
  if a <= b then a else b

(* Temporal: once p   == p has been true at some point so far. *)
let once (p: stream bool): stream bool =
  let rec r = p || (false `fby` r) in
  r

(* Temporal: sofar p  == p has been true at every step so far. *)
let sofar (p: stream bool): stream bool =
  let rec r = p && (true `fby` r) in
  r

(* --- countsecutive --------------------------------------------------- *)

(* Saturating counter of consecutive `p` ticks. *)
let count_max: int = 65535

[@@proof_induct1]
let countsecutive (p: stream bool): stream int =
  let rec count =
    if p
    then min ((0 `fby` count) + 1) count_max
    else 0
  in
  check (0 <= count);
  count

(* --- lastn / anyn ---------------------------------------------------- *)

let lastn (n: int) (p: stream bool): stream bool =
  countsecutive p >= n

let anyn (n: int) (p: stream bool): stream bool =
  countsecutive (not p) < n

(* --- controller ------------------------------------------------------ *)

let settle_time: int = 1000
let stuck_time:  int = 6000

[@@proof_induct1]
let controller_body (estop level_low: stream bool): stream (bool & bool) =
  let sol_try   = lastn settle_time (not estop && level_low) in
  let nok_stuck = once (lastn stuck_time sol_try) in
  let sol_en    = sol_try && not nok_stuck in
  check (estop ==>^ not sol_en);
  check (not level_low ==>^ not sol_en);
  (sol_en, nok_stuck)

(* Pair-input wrapper around [controller_body], suitable for the
  [Pipit.Plugin.Extract.extract] splice which currently only supports
  stream functions of a single argument. *)
let controller (i: stream (bool & bool)): stream (bool & bool) =
  let (estop, level_low) = i in
  controller_body estop level_low

(* --- reservoir / spec (no proofs) ------------------------------------ *)

(* Simple reservoir model. The level is the integral of inflow minus
  outflow, where the outflow is gated by [sol_en]: when the solenoid is
  closed (sol_en = false) any positive inflow still enters but a negative
  inflow (drain) is forced to zero. *)
let reservoir_model (flow: stream int) (sol_en: stream bool): stream int =
  let rec level =
    (0 `fby` level) + (if sol_en then flow else min flow 0)
  in
  level

let max_flow:            int = 10
let level_low_threshold: int = 80
let max_level:           int = 100

(* Full system spec. Calls [controller_body] (whose own [check]s get
  inlined into the induction obligation) and reuses its [sol_en] output. *)
[@@proof_induct1]
let spec_body (flow: stream int) (estop level_low: stream bool): stream unit =
  let (sol_en, _) = controller_body estop level_low in
  let level       = reservoir_model flow sol_en in
  check
    (sofar (abs flow < max_flow) ==>^
    (sofar (level > level_low_threshold ==>^ not level_low) ==>^
    (level < max_level)))

(* Variant that introduces a manual CSE invariant
  countsecutive (x && y) <= countsecutive y. With the extra invariant the
  original example/Pump.Check version goes through 1-induction. *)
[@@proof_induct1]
let spec_any_needs_extra_invariant_manual_cse
    (flow: stream int) (estop level_low: stream bool): stream unit =
  let sol_try_c   = countsecutive (not estop && level_low) in
  let level_low_c = countsecutive level_low in
  let sol_try     = sol_try_c >= settle_time in
  let nok_stuck   = once (lastn stuck_time sol_try) in
  let sol_en      = sol_try && not nok_stuck in
  let level       = reservoir_model flow sol_en in
  check (sol_try_c <= level_low_c);
  check
    (sofar (abs flow < max_flow) ==>^
    (sofar (level > level_low_threshold ==>^ (level_low_c < settle_time)) ==>^
    (level < max_level)))
