module Network.TTCan.Impl.Util

module S       = Pipit.Sugar.Shallow
module U64     = Network.TTCan.Prim.U64
module S32R    = Network.TTCan.Prim.S32R

open Pipit.Sugar.Shallow.Tactics.Lift
open Network.TTCan.Types

(**** Edges ***)

(* True when value changes; initially true (stream transitions from bottom to value) *)
let edge
  (#a: eqtype) {| S.has_stream a |}
  (v: stream a)
    : stream bool =
  true ->^ (v <> pre v)

(* True when value transitions to true; initially true when v initially true (stream transitions from bottom to true) *)
let rising_edge
  (v: stream bool)
    : stream bool =
  v && not (false `fby` v)

(* True when value transitions FROM true; initially false regardless of v (stream transitions from bottom to value) *)
let falling_edge
  (v: stream bool)
    : stream bool =
  not v && (false `fby` v)

(* Check whether the value stream `v` only changes when clock `k` is true.
  (That is, if v is sampled on k)

  This is related to `edge`, in that:
  > is_sampled_on v (edge v)
  always holds

  *)
let is_sampled_on
  (#a: eqtype) {| S.has_stream a |}
  (v: stream a)
  (k: stream bool)
    : stream bool =
  true ->^ (v = pre v || k)

(* Resettable latch.
  Named arguments would be nice. It's easy to confuse the set/reset so we
  package them up in a record.
*)
type latch_args = { set: bool; reset: bool }

instance has_stream_latch_args: S.has_stream latch_args = {
  ty_id = [`%latch_args];
  val_default = { set = false; reset = false; };
}

[@@FStar.Tactics.preprocess_with preprocess]
let latch (args: stream latch_args): stream bool =
  let rec latch =
    if args.set
    then true
    else if args.reset
    then false
    else (false `fby` latch)
  in latch

(**** Time utilities ***)

(* The driver performs a "tick" at least every ttcan_exec_period ntus.
  The time must be increasing and increase by at most ttcan_exec_period.
  The initial value of the time does not necessarily need to be 0.
*)
let local_time_valid (cfg: config) (local_time: stream ntu): stream bool =
  let open U64 in
  let prev = pre local_time in
  let next = prev + S32R.s32r_to_u64 cfg.triggers.ttcan_exec_period in
  true ->^ (prev < local_time && local_time <= next)

(* The cycle time is the time relative to the start of the current basic cycle.
  Whenever the reference clock indicates the start of a new basic cycle, the
  cycle time resets. We allow a period's slack time between the actual reset and
  the reference clock, as the driver might not be called immediately.
*)
let cycle_time_valid (cfg: config) (ref_ck: stream bool) (cycle_time: stream ntu): stream bool =
  let open U64 in
  let ttcan_exec_period = S32R.s32r_to_u64 cfg.triggers.ttcan_exec_period in
  let prev = pre cycle_time in
  let next = prev + ttcan_exec_period in
  // Reset on first step and on reference clock
  if true ->^ ref_ck
  then cycle_time < ttcan_exec_period
  else prev < cycle_time && cycle_time <= next


%splice[] (autolift_binds [`%edge; `%rising_edge; `%falling_edge; `%is_sampled_on; `%latch; `%local_time_valid; `%cycle_time_valid])
