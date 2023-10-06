module Network.Check

open Network.Abstract

open Pipit.Sugar.Vanilla
module Table = Pipit.Prim.Vanilla

let times = ints

let message_id_opt  = Table.TInt
let message_id_opts = s message_id_opt
let message_id_none'  = 0
let message_id_none: message_id_opts = const message_id_none'

let send_status   = Table.TBool
let send_statuses = s send_status
let send_status_ok:  send_statuses = const true
let send_status_nok: send_statuses = const false

let sender_result = Table.TPair message_id_opt (Table.TPair Table.TInt Table.TInt)
let sender_results = s sender_result
let sender_results_msg_id (s: sender_results): message_id_opts = fst s
let sender_results_drop_count (s: sender_results): ints = fst (snd s)
let sender_results_age (s: sender_results): ints = snd (snd s)

let sender_results_make (msg_id: message_id_opts) (drop_count: ints) (age: ints): sender_results = tup msg_id (tup drop_count age)


let schedule_send_at (#n: network) (s: schedule n) (m: n.message) (now: times): bools =
  now %^ (n.message_info m).period =^ const (s.phases m)

let rec scheduled_send_messages (#n: network) (s: schedule n) (node: n.node) (ms: list n.message) (now: times): message_id_opts =
  match ms with
  | [] -> message_id_none
  | m :: ms' ->
    if_then_else (schedule_send_at s m now)
      (const (n.message_info m).message_id)
      (scheduled_send_messages s node ms' now)

let scheduled_send (#n: network) (s: schedule n) (node: n.node): times -> message_id_opts =
  scheduled_send_messages s node (node_send_list node)

let message_id_priority_ge (a b: message_id_opts): bools =
  (a <>^ message_id_none) /\ (a <=^ b)

let message_id_better (a b: message_id_opts): message_id_opts =
  if_then_else
    (b =^ message_id_none)
    a
    (if_then_else (a <=^ b) a b)

(*
  let node sender (send_req: option message_id) (pre_status: send_status): sender_result =
    let rec
      ok   = (pre_status = OK)
      send = if ok \/ drop then send_req else pre send;
      drop = send_req `higher_priority_than` pre send;
      age  = countsecutive (not ok /\ not drop);
      drop_count = count drop;
    in
      { send = send; drop_count = drop_count; age = age; }
*)
let sender (send_req: message_id_opts) (pre_status: send_statuses): sender_results =
  let' (pre_status =^ send_status_ok) (fun ok ->
  letrec2 (fun send drop ->
  // send =
    if_then_else (ok \/ drop) send_req (pre send)
  ) (fun send drop ->
  // drop =
    message_id_priority_ge send_req (pre send)
  ) (fun send drop ->
  let' (countsecutive (!^ ok /\ !^ drop)) (fun age ->
  let' (count drop) (fun drop_count ->
    sender_results_make send drop_count age))))

let router_send (#n: network) (s: schedule n) (node: n.node) (pre_status: send_statuses) (now: times): sender_results =
  let sched = scheduled_send s node now in
  sender sched pre_status



