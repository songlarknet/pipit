module Network.TTCan.Impl.Util
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

module U64     = Network.TTCan.Prim.U64
module S32R    = Network.TTCan.Prim.S32R

open Network.TTCan.Types

(* One-cycle delay; on the first cycle returns the type's default value. *)
let pre
  (#a: eqtype) {| PSSB.has_stream a |}
  (v: stream a)
    : stream a =
  PSSB.val_default `fby` v

(* True when value changes; initially true *)
let edge
  (#a: eqtype) {| PSSB.has_stream a |}
  (v: stream a)
    : stream bool =
  if true `fby` false then true else (v <> pre v)

(* True when value transitions to true; initially true when v initially true *)
let rising_edge
  (v: stream bool)
    : stream bool =
  v && not (pre v)

(* True when value transitions FROM true; initially false regardless of v *)
let falling_edge
  (v: stream bool)
    : stream bool =
  not v && pre v

(* Check whether the value stream `v` only changes when clock `k` is true. *)
let is_sampled_on
  (#a: eqtype) {| PSSB.has_stream a |}
  (v: stream a)
  (k: stream bool)
    : stream bool =
  if true `fby` false then true else (v = pre v || k)

(* Resettable latch. *)
[@@derive_has_stream]
type latch_args = { set: bool; reset: bool }

let latch (args: stream latch_args): stream bool =
  rec' (fun l ->
    if args.set
    then true
    else if args.reset
    then false
    else pre l)

(**** Time utilities ***)

let local_time_valid (cfg: config) (local_time: stream ntu): stream bool =
  let prev = pre local_time in
  let next = U64.op_Plus prev (S32R.s32r_to_u64 cfg.triggers.ttcan_exec_period) in
  if true `fby` false
  then true
  else (U64.op_Less prev local_time && U64.op_Less_Equals local_time next)

let cycle_time_valid (cfg: config) (ref_ck: stream bool) (cycle_time: stream ntu): stream bool =
  let ttcan_exec_period = S32R.s32r_to_u64 cfg.triggers.ttcan_exec_period in
  let prev = pre cycle_time in
  let next = U64.op_Plus prev ttcan_exec_period in
  if (if true `fby` false then true else ref_ck)
  then U64.op_Less cycle_time ttcan_exec_period
  else U64.op_Less prev cycle_time && U64.op_Less_Equals cycle_time next
