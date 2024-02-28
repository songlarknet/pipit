module Network.TTCan.Impl.Util

module S       = Pipit.Sugar.Shallow
module U64     = Network.TTCan.Prim.U64

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


let time_ascending (local_time: stream ntu): stream bool =
  let open U64 in
  0uL `fby` local_time < local_time

%splice[] (autolift_binds [`%edge; `%rising_edge; `%falling_edge; `%latch; `%time_ascending])
