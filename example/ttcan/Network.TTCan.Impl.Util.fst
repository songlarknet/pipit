module Network.TTCan.Impl.Util

module S       = Pipit.Sugar.Shallow
module U64     = Network.TTCan.Prim.U64

open Network.TTCan.Types

(**** Edges ***)

(* True when value changes; initially true (stream transitions from bottom to value) *)
let edge
  (#a: eqtype) {| S.has_stream a |}
  (v: S.stream a)
    : S.stream bool =
  let open S in
  (const true) ->^ (v <> pre v)

(* True when value transitions to true; initially true when v initially true (stream transitions from bottom to true) *)
let rising_edge
  (v: S.stream bool)
    : S.stream bool =
  let open S in
  v /\ ~ (false `fby` v)

(* True when value transitions FROM true; initially false regardless of v (stream transitions from bottom to value) *)
let falling_edge
  (v: S.stream bool)
    : S.stream bool =
  let open S in
  ~ v /\ (false `fby` v)


(* Resettable latch.
  Named arguments would be nice. It's easy to confuse the set/reset so we
  package them up in a record.
*)
noeq
type latch_args = { set: S.stream bool; reset: S.stream bool }

let latch (args: latch_args): S.stream bool =
  let open S in
  rec' (fun latch ->
    if_then_else args.set (const true)
      (if_then_else args.reset (const false) (false `fby` latch)))


let time_ascending
  (local_time: S.stream ntu)
    : S.stream bool =
  let open S in
  let open U64 in
  0uL `fby` local_time < local_time
