(*
  Simplifications and unsupported features:
  * no arbitration windows
  * level 1 only (reference messages do not include global time)
  * no gaps between basic cycles ("Next In Gap")
  * no watchdog

  Some changes are a result of the design:
  * configuration is static; no configuration mode
  * no Tx_Ref_Trigger and Watch_Trigger triggers

  Terminology: master / follower


  Comments preceded with a hat (^) are references to TTCAN ISO standard 11898-4:2004(E)
*)
module Network.TTCan

module List = FStar.List.Tot
module U8 = FStar.UInt8
module S8 = FStar.Int8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(********* BASE DEFINITIONS ********)
(* For static configuration, we can use regular integers; for runtime values, we need to use machine integers. *)
type subrange (i: int) (j: int) = n: int { i <= n /\ n <= j }

type sub8 (i: subrange 0 255) (j: subrange 0 255) = n: U8.t { i <= U8.v n /\ U8.v n <= j }
type sub16 (i: subrange 0 65535) (j: subrange 0 65535) = n: U16.t { i <= U16.v n /\ U16.v n <= j }

(********* CAN ********)
(* TODO: specify extended CAN identifiers *)
type can_id = U32.t

(*^ NTU: unit measuring all times and providing a constant of the whole network *)
(* A time in network-time-units, which is the time for a bit to be broadcast on the bus: roughly 1µs for a 1Mbps bus.
  The TTCAN standard specifies that 16 bits is enough for NTUs, but that means
  that an NTU clock will overflow multiple times per second. This overflow
  behaviour is fine for an implementation, but it complicates the specification.
  Instead, for the first version, we'll use 64-bit NTUs which we can safely
  assume will never overflow.
 *)
type ntu    = U64.t

type can_message 'a = {
  (* start-of-frame time *)
  can_message_sof:   ntu;
  can_message_id:    can_id;
  can_message_value: 'a;
}

(* CAN messages with an 8-byte maximum payload *)
type can_message_bytes = {
  can_message_len: sub8 0 8;
  // TODO: ensure bytes past message_len are zeroed out
  // message_u64: u64: U64.t { u64 & ~(mask message_len) = 0 };
  can_message_u64: U64.t;
}

type can_message_bytes' = can_message can_message_bytes

// noeq
// type can_encoder 'a = {
//   bytes_of_message: 'a -> can_message_bytes;
//   message_of_bytes: can_message_bytes -> option 'a;
//   max_message_len: subrange 0 8;
//   lemma_roundtrip: squash (forall (a: 'a). message_of_bytes (bytes_of_message a) == Some a);
//   lemma_max_bytes: squash (forall (a: 'a). U8.v (bytes_of_message a).can_message_len <= max_message_len);
// }

(********* TTCAN RUNTIME VALUES ********)

let tt_cycle_count_max       = 63
let tt_time_master_index_max = 7
(* Message status count: 3-bit saturating error count *)
(*^ MSC: error counter providing means for detecting scheduling errors for messages sent in exclusive time windows *)
type tt_msc                  = sub8 0 7

(*^ Master reference message (level 1) *)
type tt_reference_message = {
  (*^ Next_Is_Gap: *)
  next_is_gap: bool;
  (*^ Cycle_Count: number of the current basic cycle of the matrix cycle *)
  cycle_count: sub8 0 tt_cycle_count_max
}

type tt_reference_message' = can_message tt_reference_message

let ttcan_id_is_master_ref (can_id: can_id): bool =
  U32.v can_id <= tt_time_master_index_max

(********* TTCAN STATIC CONFIGURATION ********)

type tt_trigger_schedule = {
  (*^ Repeat_Factor: parameter specifying the repetition rate of a message within a transmission column, being a part of Tx_Trigger or Rx_Trigger parameters *)
  repeat_factor: subrange 1 64; // TODO: restrict to pow-2
  (*^ Cycle_Offset: parameter specifying, within a matrix cycle, the first basic cycle for which an Rx_Trigger or Tx_Trigger is valid *)
  cycle_offset:  subrange 0 (repeat_factor - 1)
}

(* Trigger-specific options *)
type tt_trigger_type =
  | Tx_Trigger:
    (* if true, clear "TX pending" bit in associated message buffer after fires.
       for a sequence of redundant transmissions, only the last should be set to clear pending. *)
    clear_pending: bool ->
    tt_trigger_type
  | Rx_Trigger:
    tt_trigger_type

(* TX and RX triggers *)
type tt_trigger 'm = {
  trigger_message:  'm;
  trigger_schedule: tt_trigger_schedule;
  trigger_type:     tt_trigger_type;
}

noeq
type tt_message_info 'node = {
  sender:  'node;
  read_by: 'node -> bool;
  can_id:  c: can_id { ~ (ttcan_id_is_master_ref c) };

  // payload:  eqtype;
  // encoder: can_encoder payload;
}

type tt_node_transmission_column 'm = {
  triggers: list (tt_trigger 'm);
}

noeq
type tt_node_info 'node 'm = {
  time_master_priority: option (subrange 0 tt_cycle_count_max);
  matrix: list (tt_node_transmission_column 'm);
  (* Initial_Ref_Offset: per-node configuration for masters *)
  initial_ref_offset: S8.t;

  (*^ Tx_Enable is (a time window that is) opened with Tx_Trigger and closed after a predefined number of nominal CAN bit times specified by the system configuration *)
  tx_enable_window: nat;
}

noeq
type tt_network = {
  node: eqtype;
  message: eqtype;

  node_info: node -> tt_node_info node message;
  message_info: message -> tt_message_info node;

  time_mark_ends: list ntu; // increasing with suitable gaps, eg gap of 128µs ~ 16,000 cycles @ 125MHz
  // rx_ref_trigger_time: nat; // all p. time_mark_ends <= rx_ref_trigger_time
  tx_ref_trigger_time: nat; // rx_ref_trigger_time <= tx_ref_trigger_time
  watch_trigger_time:  nat; // tx_ref_trigger_time < watch_trigger_time
  // basic_cycle_duration: nat;
  cycle_count_max: subrange 0 tt_cycle_count_max;

  (* error if we go this long without receiving a reference message *)
}

(*^ Error severity: no error (S0), warning (S1), error (S2) and severe error (S3) *)
type tt_error_severity = sub8 0 3
let severity_no_error: tt_error_severity = 0uy
let severity_warning:  tt_error_severity = 1uy
let severity_error:    tt_error_severity = 2uy
let severity_severe:   tt_error_severity = 3uy

type tt_master_mode = | MasterOff | Follower | BackupMaster | CurrentMaster

type tt_sync_state = | Configuration | SyncOff | Synchronising | InSchedule // | InGap -- gaps not supported yet

type tt_faultbits = {
  tt_scheduling_error1: bool; // S1
  // tt_tx_underflow:      bool;
  tt_scheduling_error2: bool; // S2
  // tt_tx_overflow:       bool;
  tt_can_bus_off:       bool; // S3
  // tt_config_error:      bool;
  tt_watch_trigger_reached: bool;
}

type tt_send_status = | SendOk | SendAborted | SendLostArbitration | SendError | SendPending

(*****SPEC***)

noeq
type ttcan_state (net: tt_network) = {
  tt_error_severity: tt_error_severity;
  tt_master_mode: tt_master_mode;
  tt_sync_state: tt_sync_state;

  (*^ Local_Time *)
  local_time: ntu;
  (*^ Ref_Mark: Sync_Mark time of active reference message *)
  ref_mark: rm: ntu { U64.v rm <= U64.v local_time };
  (*^ Ref_Trigger_Offset: [-127, 127] *)
  ref_trigger_offset: S8.t;

  (* cycle_time < net.basic_cycle_duration => ... *)
  cycle_time: ntu;
  // global_time: ntu; // level 2 only?
  cycle_count: sub8 0 net.cycle_count_max;

  tt_faultbits: tt_faultbits;

  msc_per_message: net.message -> tt_msc;

  // wait_for_event: bool; -- true if Next_Is_Gap was true on previous ref
  // TUR_Actual: Q -- required for level 2
}


noeq
type ttcan_result (net: tt_network) = {
  ttcan_state: ttcan_state net;
  ttcan_tx_enabled: bool;
  ttcan_tx: option can_message_bytes';
}

// let ttcan_init = { tt_error_severity = severity_no_error; tt_master_mode = MasterOff; tt_sync_state = SyncOff; }

// big number, eg 2^64-1
assume val tt_local_time_max: U64.t

let ttcan_step (#net: tt_network)
  (st: ttcan_state net { U64.v st.local_time < U64.v tt_local_time_max })
  (rx: option (msg: can_message_bytes' { U64.v msg.can_message_sof < U64.v st.local_time }))
  (send_status: tt_send_status)
  // (start_sync: bool)
  : ttcan_result net =
 let local_time = U64.(st.local_time `add` 1uL) in
 let cycle_time = U64.(local_time `sub` st.ref_mark) in

 admit ()

(* Pipit:

let%node ttcan_node (#net: static tt_network) (node: static net.node)
  (set_config_mode: option bool)
  (rx: option can_message_bytes')
  (send_status: send_status)
  returns
  (
    can_enable_acks: bool;
    tx: option can_message_bytes';

    error_severity: tt_error_severity;
    master_mode: tt_master_mode;
    sync_state: tt_sync_state;
    faultbits: tt_faultbits;

    local_time: ntu;
    ref_mark: ntu;
    ref_trigger_offset: S8.t;

    cycle_time: ntu;

    cycle_count: sub8 0 net.cycle_count_max;

    msc_per_message: net.message -> tt_msc;
  ) =
let
  pre_error_severity = tt_error_severity_no_error `fby` error_severity;
  pre_master_mode = MasterOff `fby` master_mode;
  pre_sync_state = Configuration `fby` sync_state;
  pre_faultbits = _ `fby` faultbits;

  local_time = 0 `fby` (local_time + 1);
  cycle_time = local_time - cycle_time_start;

  //^ Cycle_Time shall be zero when the state "synchronising" is entered
  cycle_time_start =
    if rising(sync_state = Synchronising)
    then local_time
    else if new_ref_mark then new_ref_mark.message_sof
    else pre cycle_time_start

  //^ S3- severe error: all CAN bus operations are stopped
  can_enable_acks = sync_state <> Configuration /\ error_severity <> error_severity_severe;

  match pre_sync_state with
  | Configuration ->
    let
      can_enable_acks = false;
  | Synchronising ->
    if cycle_time > init_watch_trigger_time
    then sync_state = SyncOff

    //^ After reset, a FSE shall consider itself synchronised to the network after the occurrence of the second consecutive reference message
    if new_ref_mark and ref_mark_valid and (false `fby` pre ref_mark_valid)
    then sync_state = InSchedule

    //^ When a failed time master reconnects to the system with active tie-triggered communication, it shall wait until it is synchronised to the network before attempting to become time master again.
    if previously(error) and (cycle_time - ref_mark) < active_bus_timeout
    then tx_ref_request = false;

    can_enable_acks = true;
  | InSchedule ->
    if cycle_time > net.watch_trigger_time
    then sync_state = SyncOff;

    can_enable_acks = true;
  | SyncOff ->
    can_enable_acks = true;


  ref_mark =
    match new_ref with
    | None -> 0 `fby` ref_mark
    | Some r -> r.message_sof;

  take_new_ref =


  new_ref =
    if take_new_ref then
      match rx with
      | Some rx' -> if ttcan_id_is_master_ref rx.can_id then rx
      | None -> None
    else None;

  pre_ref_trigger_offset = (net.nodes node).initial_ref_offset `fby` ref_trigger_offset;
  ref_trigger_offset =
    //^ If [a potential master] becomes current time master (by successfully transmitting a reference message), it shall use Ref_Trigger_Offset = 0.
    if pre_master_mode = CurrentMaster
    then 0
    //^ [At error level S2,] potential masters may still transmit reference messages with the Ref_Trigger_Offset set to the maximum value of 127.
    else if error_severity = severity_error
    then 127
    else if master_downgrade_to_backup
    then (net.nodes node).initial_ref_offset
    else if ref_master_index > (net.nodes node).master_index
    then
      (if pre_ref_trigger_offset > 0
       then 0
       // XX: only when sync_state = InSchedule?
       else if new_basic_cycle
       then pre_ref_trigger_offset - 1
       else pre_ref_trigger_offset)
    else pre_ref_trigger_offset;

  //^ Any time a potential master receives a reference message with a higher priority than its own, it shall use Ref_Trigger_Offset = Initial_Ref_Offset and shall change its master state to backup time master.
  master_downgrade_to_backup =
    pre_master_mode = CurrentMaster /\ ref_master_index < (net.nodes node).master_index;

  tx_ref_trigger = net.tx_ref_trigger_time + ref_trigger_offset;

  watch_trigger =
    pre_sync_state = InSchedule and cycle_time >= net.watch_trigger_time;

  //^ Whenever a Tx_Ref_Trigger (+Ref_Trigger_Offset) becomes active, the transmission of a reference message shall be requested.
  //^ The request shall remain active until any reference message is completed (transmitted or received).
  tx_ref_request = am_potential_master && cycle_time >= tx_ref_trigger;
  //^ When a reference message is disturbed by an error, it shall be repeated as soon as possible with updated Master_Ref_Mark.
  //^ Each FSE shall provide a Watch_Trigger that becomes active when an expected reference message is missing for too long.


  faultbits = ...;


  error_severity = error_summary faultbits;
  master_mode = ...;
  sync_state = ...;

  tx =
    match sync_state with
    | Configure -> None
    | SyncOff -> None
    //^ Until a FSE is synchronised to the network, it shall not transmit a message (except potential time masters may submit reference messages)
    | Synchronising -> master refs only
    | InSchedule ->
      if error_severity < severity_error
      then all enabled
      else master refs only
  ;

  msc_per_message =
    match sync with
    //^ Until a FSE is synchronised to the network, it shall not update the MSCs of the message objects
    | Configure | SyncOff | Synchronising -> pre msc_per_message
    | InSchedule -> ...


(*ERRORS:*)
  (*^ Scheduling_Error_1 (S1) is set if within one matrix cycle the difference between the highest MSC and the lowest MSC of all messages of exclusive time windows of a FSE is larger than 2, or if one of the MSCs of an exclusive receive message object has reached 7.
    If within one matrix cycle none of these conditions is valid, the bit is reset.
  *)
  faultbits_scheduling_error_1_set = latch(trigger = ..., reset = new_basic_cycle)
  faultbits_scheduling_error_1 = latch(trigger = faultbits_scheduling_error_1_set, reset = new_basic_cycle and not faultbits_scheduling_error_1_set);


  (*^ Scheduling_Error_2 (S2) is set if for one transmit message object the MSC has reached 7. It is reset when no transmit object has an MSC of seven. *)
  faultbits_scheduling_error_2 = ...;

  (*^ CAN_Bus_Off (S3): the controller went bus-off due to CAN-specific errors *)
  faultbits_can_bus_off = latch(trigger = can_bus_off; reset = reset_s3_error);

  (*^ Watch_Trigger_Reached (S3): *)
  (*^ The S3 error conditions shall remain active until the application updates the configuration. *)
  faultbits_watch_trigger_reached = latch(trigger = watch_trigger, reset = reset_s3_error);

  reset_s3_error = (Some? set_config_mode);

  (* Errors not treated: Tx_Underflow, Tx_Overflow, Config_Error statically excluded; Application_Watchdog not supported *)



tel
*)

 let error_summary (faults: tt_faultbits): tt_error_severity =
   if faults.tt_can_bus_off || faults.tt_watch_trigger_reached
   then severity_severe
   else if faults.tt_scheduling_error2
   then severity_error
   else if faults.tt_scheduling_error1
   then severity_warning
   else severity_no_error

