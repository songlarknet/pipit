(* Simplified version of trigger fetch logic with timeliness proof.
  This abstracts some details of the trigger fetch itself:
  1. we ignore Ref_Trigger_Offset, which dynamically adjusts the time mark for
     Tx_Ref_Triggers by [-127,127];
  2. we use arbitrary-sized integer arithmetic for indices and times, which
     reduces some syntactic noise;
  3. we use a simple tick-based time instead of microseconds;
  4. no reset trigger;
  5. cycle offset is assumed to be constant, rather than taking a new value
     every reset.
*)
module Network.TTCan.TriggerTimely

module S     = Pipit.Sugar.Shallow

open Pipit.Sugar.Shallow.Tactics.Lift

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics
module Check     = Pipit.Sugar.Check
module Contract  = Pipit.Sugar.Contract
module T = Pipit.Tactics

instance has_stream_int: S.has_stream int = {
  ty_id = [`%int];
  val_default = 0;
}

type index = int
(* Tick-based logical time; one message per tick *)
type time  = int
(* Cycle index < 64 *)
type cycle = int

(* Abstract functional representation of triggers array. In the implementation,
  this is backed by functions that read from a const array. Here, we just
  reason about it abstractly. *)
noeq
type trigger_array = {
  size:      nat;
  enabled:   index -> cycle -> bool;
  time_mark: index -> time;
}

(*** Time-marks are sorted:
  The time-marks in an array must be *nondecreasingly* sorted. Duplicate
  time-marks are allowed, as long the two triggers are not enabled in the same
  cycle (formalised below).
*)
let time_mark_sorted_req (triggers: trigger_array): prop =
  forall (i: index { i < triggers.size - 1 }).
    triggers.time_mark i <= triggers.time_mark (i + 1)

(*** Adequate spacing:
  If two triggers, i and j, are enabled in the same cycle, then their time
  marks must be far enough apart that we have time to iterate through the
  indices from i to j.
*)
let adequate_spacing (triggers: trigger_array) (i j: nat) (c: cycle): prop =
  i < triggers.size                  ==>
  j < triggers.size                  ==>
  i <= j                             ==>
  triggers.enabled i c               ==>
  triggers.enabled j c               ==>
  (triggers.time_mark j - triggers.time_mark i) >= (j - i)

let adequate_spacing_req (triggers: trigger_array): prop =
  forall (i j: nat). forall (c: cycle).
    adequate_spacing triggers i j c

(*** Time-marks are reachable from start:
  After a reset, we need to be able to get from index 0 to the first enabled
  time-mark i before it starts. This should hold in general too.
*)
let time_mark_reachable_req (triggers: trigger_array): prop =
  forall (i: index { 0 <= i /\ i < triggers.size }).
    i <= triggers.time_mark i

(* Static trigger configuration with proofs of the above properties *)
noeq
type config = {
  triggers:                trigger_array;
  time_mark_sorted_req:    squash (time_mark_sorted_req triggers);
  adequate_spacing_req:    squash (adequate_spacing_req triggers);
  time_mark_reachable_req: squash (time_mark_reachable_req triggers);
  size_req:                squash (triggers.size > 0);
}


(* Find next enabled trigger or None *)
let rec next (triggers: trigger_array) (ix: int) (c: cycle)
  : Tot (option (j: index { j < triggers.size /\ (triggers.enabled j c) /\ ix <= j })) (decreases (triggers.size - ix)) =
  if ix < 0 || ix >= triggers.size
  then None
  else if triggers.enabled ix c
  then Some ix
  else (
    match next triggers (ix + 1) c with
    | Some i -> Some i
    | None -> None
  )

let lemma_adequate_spacing_next_inc_pattern (cfg: config) (c: cycle) (index: index) = ()

let lemma_adequate_spacing_next_inc (cfg: config) (c: cycle) (index: index)
  : Lemma
    (ensures (
      match next cfg.triggers (index + 1) c with
      | None -> True
      | Some n ->
        0 <= index ==>
        adequate_spacing cfg.triggers index n c
    ))
    [SMTPat (lemma_adequate_spacing_next_inc_pattern cfg c index)]
  = ()

let trigger_index_invariant (cfg: config) (c: cycle) (now: time) (index: index): bool =
  match next cfg.triggers index c with
  | None -> true
  | Some n -> (cfg.triggers.time_mark n - now) >= (n - index)

let id (#a: Type) (x: a): a = x

[@@source; FStar.Tactics.preprocess_with preprocess]
let count_when (max: nat) (inc: stream bool): stream int =
  rec' (fun count ->
    check (0 <= count && count <= max);
    let count' = (0 `fby` count) + (if inc then 1 else 0) in
    if count' > max then max else count')

%splice[count_when_core] (autolift_binds [`%count_when])


[@@lifted; of_source(`%count_when)]
let count_when_checked (max: nat): S.stream bool -> S.stream int =
  let e = Check.exp_of_stream1 (count_when_core max) in
  assert (Check.system_induct_k1 e) by (T.pipit_simplify []);
  Check.stream_of_checked1 e

[@@source; FStar.Tactics.preprocess_with preprocess]
let time_increasing (now: stream int): stream bool =
  now = (0 `fby` (now + 1))

(* Lift array accessors to streaming primitives *)
[@@source; FStar.Tactics.preprocess_with preprocess]
let trigger_enabled (cfg: config) (index: stream index) (c: cycle): stream bool =
  cfg.triggers.enabled index c

[@@source; FStar.Tactics.preprocess_with preprocess]
let trigger_time_mark (cfg: config) (index: stream index): stream time =
  cfg.triggers.time_mark index

%splice[time_increasing_core; trigger_enabled_core; trigger_time_mark_core] (autolift_binds [`%time_increasing; `%trigger_enabled; `%trigger_time_mark])


[@@source; FStar.Tactics.preprocess_with preprocess]
let trigger_index (cfg: config) (c: cycle) (now: stream time): stream index =
  rec' (fun index ->
    let inc = false `fby` ((trigger_time_mark cfg index <= now || not (trigger_enabled cfg index c))) in
    let index = count_when cfg.triggers.size inc in

    lemma_pattern (lemma_adequate_spacing_next_inc_pattern cfg c index);
    check (trigger_index_invariant cfg c now index);
    // We should really be able to put a `time_increasing` precondition on here:
    // but we run into problems proving the contract below, because the state inside `sofar`
    // is a different one to the one in the contract. Common subexpression elimination would help here:
    // check "" (sofar (time_increasing now) ==> (lift2 (fun now index -> trigger_index_invariant cfg c now index)) now index);^
    index)

%splice[trigger_index_core] (autolift_binds [`%trigger_index])

[@@source; FStar.Tactics.preprocess_with preprocess]
let trigger_fetch_guar (cfg: config) (c: cycle) (index: stream int) (now: stream int): stream bool =
  let (==>) (a b: bool): bool = if a then b else true in
  (index < cfg.triggers.size && trigger_enabled cfg index c) ==> trigger_time_mark cfg index >= now

%splice[trigger_fetch_guar_core] (autolift_binds [`%trigger_fetch_guar])

// TODO: no tactic for contract syntax yet. so we stub out the fake "source" contract,
// and then implement it and check it below
assume val trigger_fetch (cfg: config) (c: cycle): stream int -> stream index

[@@lifted; of_source(`%trigger_fetch)]
let trigger_fetch_checked (cfg: config) (c: cycle): S.stream int -> S.stream index =
  let open S in
  let c = Contract.contract_of_stream1 {
    rely = time_increasing_core;
    guar = trigger_fetch_guar_core cfg c;
    body = trigger_index_core cfg c;
  } in
  assert (Contract.system_induct_k1 c) by (T.pipit_simplify_products []);
  Contract.stream_of_contract1 c
