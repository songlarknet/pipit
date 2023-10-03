module Network.Can.Check

type u8    = nat
type u64   = nat
type bytes = { data: u64; }

noeq
type message_info 'node = {
  sender:   'node;
  listens:  'node -> bool;

  payload:  eqtype;
  priority: int;
  period:   nonzero;

  // bytes_of_message: payload -> bytes;
  // message_of_bytes: bytes -> option payload;
}

noeq
type network = {
  node:    eqtype;
  message: eqtype;
  message_info: message -> message_info node;
  messages: list message;
}

noeq
type schedule (n: network) = {
  phases: n.message -> nat;
  lcm: nat;
}

let schedule_msg_ok (#n: network) (s: schedule n): prop =
  forall (m0: n.message) (m1: n.message { not (m0 = m1) }).
    let mi0 = n.message_info m0 in
    let mi1 = n.message_info m1 in
    let ph0 = s.phases m0 in
    let ph1 = s.phases m1 in
    forall (time: nat).
      (time % mi0.period = ph0) ==> not (time % mi1.period = ph1)

let schedule_lcm_ok (#n: network) (s: schedule n): prop =
  forall (m0: n.message).
    let mi0 = n.message_info m0 in
    let ph0 = s.phases m0 in
    (s.lcm % mi0.period = 0) /\ (ph0 < mi0.period)

let schedule_ok (#n: network) (s: schedule n): prop =
  schedule_msg_ok s /\ schedule_lcm_ok s



let rec send_trigger (#n: network) (s: schedule n) (ms: list n.message) (time: nat): option n.message =
  match ms with
  | [] -> None
  | m :: ms' ->
    if time % (n.message_info m).period = s.phases m
    then Some m
    else send_trigger s ms' time

(*
let rec sender (#m: eqtype)
  (send_request: stream (option m))
  (prev_send_ok: stream bool)
  : stream (option m & int) =
    rec' (fun (request, age) ->
      let prev_request = none `fby` request in
      let can_handle_request =
        (prev_send_ok \/ prev_request = none \/ priority send_request >= priority prev_request) in
      let request =
        if can_handle_request
        then send_request
        else prev_request
        in
      let age =
        if can_handle_request
        then 0
        else if request = none
        then -1
        else (0 `fby` age) + 1
      in
      (request, age)
    )
*)



(* Example instantiation *)
type car_node =
  | ADAS | BRAKE
type car_message =
  | ADAS'status | ADAS'brake_cmd
  | BRAKE'status

type adas'status'payload    = { ok: bool; }
type adas'brake_cmd'payload = { brake_target: option u8; }
type brake'status'payload   = { engage: bool; brake_target: u8; }

let adas'status'info: message_info car_node = {
  sender   = ADAS;
  listens  = (fun n -> match n with | ADAS -> false | BRAKE -> true);
  payload  = adas'status'payload;
  priority = 100;
  period   =  10;
}

let adas'brake_cmd'info: message_info car_node = {
  sender   = ADAS;
  listens  = (fun n -> match n with | ADAS -> false | BRAKE -> true);
  payload  = adas'brake_cmd'payload;
  priority = 100;
  period   =  10;
}

let brake'status'info: message_info car_node = {
  sender   = BRAKE;
  listens  = (fun n -> match n with | ADAS -> true | BRAKE -> false);
  payload  = brake'status'payload;
  priority = 100;
  period   =  10;
}

let car_network: network = {
  node    = car_node;
  message = car_message;

  message_info = (fun m -> match m with
    | ADAS'status    -> adas'status'info
    | ADAS'brake_cmd -> adas'brake_cmd'info
    | BRAKE'status   -> brake'status'info);

  messages = [ADAS'status; ADAS'brake_cmd; BRAKE'status];
}

let car_schedule_phases (m: car_message): nat =
  match m with
  | ADAS'status    -> 0
  | ADAS'brake_cmd -> 3
  | BRAKE'status   -> 5

let car_schedule: schedule car_network = {
  phases = car_schedule_phases;
  lcm = 10;
}

let _ =
  assert (schedule_ok car_schedule)
