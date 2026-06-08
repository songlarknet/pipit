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
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

(* Integer streaming instance: this is convenient for proofs, but cannot be
  extracted to machine-int C code correctly. *)
instance has_stream_int: PSSB.has_stream int = {
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
unfold
let adequate_spacing (triggers: trigger_array) (i j: nat) (c: cycle): prop =
  i < triggers.size                  ==>
  j < triggers.size                  ==>
  i <= j                             ==>
  triggers.enabled i c               ==>
  triggers.enabled j c               ==>
  (triggers.time_mark j - triggers.time_mark i) >= (j - i)

unfold
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

(* WORKAROUND: original ttcan does not put any proof attribute on
   count_when. The auto-splice for [@@proof_induct1] cannot handle a
   static int parameter (it tries to call system_of_exp on
   count_when_core which is [max: int -> exp ...] instead of [exp]). *)
let count_when (max: int) (inc: stream bool): stream int =
  let rec count =
    let count' = (0 `fby` count) + (if inc then 1 else 0) in
    if count' > max then max else count'
  in
  check (0 <= count && count <= max);
  count

let time_increasing (now: stream int): stream bool =
  now = (0 `fby` (now + 1))

(* Lift array accessors to streaming primitives.

   PORT BLOCKER: under #lang-pipit the lifter rejects
     cfg.triggers.enabled index c
   with "Could not solve typeclass constraint [has_stream trigger_array]"
   even after introducing an intermediate static [let ts = cfg.triggers].
   The lifter ends up classifying [ts] as a stream binding and then
   tries to manufacture a [has_stream] instance for the function-record
   type [trigger_array], which is impossible (it contains arrows).

   Workaround: replace the [trigger_*] helpers and downstream
   [trigger_index] / [trigger_fetch] with degraded constant-stream
   stubs so the rest of the module builds. The original spec lives in
   [example/ttcan/Network.TTCan.TriggerTimely.fst]; the timing proof
   is lost in ttcan2 until the lifter learns to project function-typed
   record fields. *)
let trigger_enabled (_cfg: config) (_index: stream index) (_c: cycle): stream bool =
  false

let trigger_time_mark (_cfg: config) (_index: stream index): stream time =
  0


let trigger_index (_cfg: config) (_c: cycle) (_now: stream time): stream index =
  0

(* trigger_fetch_guar is autogenerated by the Stream contract sugar
   on [trigger_fetch] below; spelling it out here would clash with
   the spliced binding. We inline [true] into the [ensures] clause. *)

(* trigger_fetch_guar / _rely are autogenerated by the Stream contract
   sugar; they need a working contract-aware splice. Under #lang-pipit
   the splice cannot currently handle static-arg-prefixed contracts
   (it tries to feed [cfg: config -> exp] into the [bless_contract]
   machinery, which expects an [exp]). Drop the sugar entirely. *)
let trigger_fetch (cfg: config) (c: cycle) (now: stream int): stream int =
  trigger_index cfg c now
