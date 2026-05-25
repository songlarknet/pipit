module Plugin.Test.Example.Pump.Check
#lang-pipit

(* A port of example/Pump.Check.fst using the #lang-pipit preprocessor.

  Each helper is a plain stream function; the [@@proof_induct1] attribute
  asks the plugin to synthesise a __check_<id> binding that discharges all
  embedded [check]s by 1-induction (norm_full []). *)

open Pipit.Source
module PSSB = Pipit.Sugar.Shallow.Base

instance has_stream_int: PSSB.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

(* --- Helpers --------------------------------------------------------- *)

let min (a b: stream int): stream int =
  if a <= b then a else b

(* Bool implication. Avoids `==>` (which is a prop-level operator). *)
let implies (a b: stream bool): stream bool =
  if a then b else true

(* Temporal: once p   == p has been true at some point so far. *)
let once (p: stream bool): stream bool =
  let rec r = if p then true else (false `fby` r) in
  r

(* Temporal: sofar p  == p has been true at every step so far. *)
let sofar (p: stream bool): stream bool =
  let rec r = if p then (true `fby` r) else false in
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
  countsecutive (if p then false else true) < n

(* --- controller ------------------------------------------------------ *)

let settle_time: int = 1000
let stuck_time:  int = 6000

[@@proof_induct1]
let controller_body (estop level_low: stream bool): stream unit =
  let sol_try   = lastn settle_time (implies estop false && level_low) in
  let nok_stuck = once (lastn stuck_time sol_try) in
  let sol_en    = sol_try && (if nok_stuck then false else true) in
  check (implies estop (if sol_en then false else true));
  check (implies (if level_low then false else true) (if sol_en then false else true))

(* TODO: port reservoir_model / spec / spec_any once `sofar`+`abs` integrate
  cleanly here. The original spec required a manual CSE invariant to be
  provable by 1-induction. *)
