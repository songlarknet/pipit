module Network.TTCan.CycleTime

module S   = Pipit.Sugar.Shallow
module U64 = Network.TTCan.Prim.U64

let stream = S.stream

type ntu = U64.t

let time_ascending (local_time: stream ntu): stream bool =
  let open S in
  let open U64 in
  sofar (0uL `fby` local_time < local_time)

let cycle_time (local_time: stream ntu)
  (reset_ck: stream bool)
  (cycle_time_capture_ck: stream bool)
  (cycle_time_capture: stream ntu) // when cycle_time_capture_ck;
    : stream ntu =
  let open S in
  let open U64 in
  let^ cycle_time_start = rec' (fun cycle_time_start ->
    if_then_else reset_ck
      local_time
    (if_then_else cycle_time_capture_ck
      cycle_time_capture
      (0uL `fby` cycle_time_start)))
  in
  let^ cycle_time = local_time - cycle_time_start in
  // check "" (time_ascending local_time /\ sofar (cycle_time_capture < local_time) ==> cycle_time <= local_time);^
  cycle_time

let top (local_time: stream ntu) (reset_ck: stream bool): stream ntu =
  cycle_time local_time reset_ck reset_ck (S.const 0uL)
