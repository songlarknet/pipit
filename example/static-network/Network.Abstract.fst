module Network.Abstract

module List = FStar.List.Tot


// CAN4LINUX:
// https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/can4linux.h?ref_type=heads
// https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/defs.h?ref_type=heads
// https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/read.c?ref_type=heads
// https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/write.c?ref_type=heads
(*
  type can_id =
    | CAN_ID_SD: bits11 -> can_id
    | CAN_ID_FD: bits29 -> can_id
*)
type can_id = nonzero // u32

type send_status =
  | NONE
  | ACK
  | ERROR
  | BUSY

let send_status_ok (s: send_status) =
  match s with | NONE | ACK -> true | _ -> false


noeq
type message_info 'node = {
  sender:   'node;
  read_by:  'node -> bool;

  message_id: can_id;
  period:   nonzero;

  payload:  eqtype;
  // bytes_of_message: payload -> bytes;
  // message_of_bytes: bytes -> option payload;
}

noeq
type network = {
  node:    eqtype;
  message: eqtype;
  message_info: message -> message_info node;
  messages: list message;
  unique_ids: squash (forall (m1 m2: message). (message_info m1).message_id = (message_info m2).message_id ==> m1 = m2);
}

let node_send_list (#n: network) (node: n.node): list n.message =
  (List.filter (fun m -> (n.message_info m).sender = node) n.messages)

let node_listen_list (#n: network) (node: n.node): list n.message =
  (List.filter (fun m -> (n.message_info m).read_by node) n.messages)

noeq
type schedule (n: network) = {
  phases: n.message -> nat;
  common_period: nat;
}

let schedule_send_at (#n: network) (s: schedule n) (m: n.message) (time: nat): bool =
  time % (n.message_info m).period = s.phases m

let schedule_msg_ok (#n: network) (s: schedule n): prop =
  forall (m0: n.message) (m1: n.message { not (m0 = m1) }).
    forall (time: nat).
      (schedule_send_at s m0 time) ==> not (schedule_send_at s m1 time)

let schedule_common_period_ok (#n: network) (s: schedule n): prop =
  forall (m0: n.message).
    let mi0 = n.message_info m0 in
    let ph0 = s.phases m0 in
    (s.common_period % mi0.period = 0) /\ (ph0 < mi0.period)

let schedule_ok (#n: network) (s: schedule n): prop =
  schedule_msg_ok s /\ schedule_common_period_ok s



let rec scheduled_send_messages (#n: network) (s: schedule n) (ms: list n.message) (time: nat): option n.message =
  match ms with
  | [] -> None
  | m :: ms' ->
    if schedule_send_at s m time
    then Some m
    else scheduled_send_messages s ms' time

let scheduled_send (#n: network) (s: schedule n) (node: n.node): nat -> option n.message =
  scheduled_send_messages s (node_send_list node)

// let 
