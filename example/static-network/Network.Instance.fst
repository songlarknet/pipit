module Network.Instance
(*
open Network.Abstract

type u8    = nat
type u64   = nat
type bytes = { data: u64; }

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
  read_by  = (fun n -> match n with | ADAS -> false | BRAKE -> true);
  message_id = 1;
  period   =  10;
  payload  = adas'status'payload;
}

let adas'brake_cmd'info: message_info car_node = {
  sender   = ADAS;
  read_by  = (fun n -> match n with | ADAS -> false | BRAKE -> true);
  message_id = 2;
  period   =  10;
  payload  = adas'brake_cmd'payload;
}

let brake'status'info: message_info car_node = {
  sender   = BRAKE;
  read_by  = (fun n -> match n with | ADAS -> true | BRAKE -> false);
  message_id = 3;
  period   =  10;
  payload  = brake'status'payload;
}

let car_network: network = {
  node    = car_node;
  message = car_message;

  message_info = (fun m -> match m with
    | ADAS'status    -> adas'status'info
    | ADAS'brake_cmd -> adas'brake_cmd'info
    | BRAKE'status   -> brake'status'info);

  messages = [ADAS'status; ADAS'brake_cmd; BRAKE'status];

  unique_ids = ();
}

let car_schedule_phases (m: car_message): nat =
  match m with
  | ADAS'status    -> 0
  | ADAS'brake_cmd -> 3
  | BRAKE'status   -> 5

let car_schedule: schedule car_network = {
  phases = car_schedule_phases;
  common_period = 10;
}

let _ =
  assert (schedule_ok car_schedule)
*)