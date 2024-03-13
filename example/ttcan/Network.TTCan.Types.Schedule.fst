(* Abstract scheduler proofs *)
module Network.TTCan.Types.Schedule

module List       = FStar.List.Tot

open FStar.Mul


noeq
type event_info 'c = {
  enabled       : 'c -> bool;
  time_mark     : 'c -> nat;

  // specification-only fields
  time_mark_min : nat;
  time_mark_max : nat;

  ok            : squash (
    forall (c: 'c).
    time_mark_min <= time_mark c /\
    time_mark c   <= time_mark_max
  );
}

noeq
type events 'c = {
  count         : nat;
  read          : n: nat { n < count } -> event_info 'c;
  exec_period   : pos;
}

let event_index (evs: events 'c) = n: nat { n <  evs.count }
let event_count (evs: events 'c) = n: nat { n <= evs.count }

(***** Requirements on trigger array ****)

(* Time-marks are sorted *)
let time_mark_sorted (evs: events 'c) (i j: event_index evs): prop =
  (evs.read i).time_mark_max <= (evs.read j).time_mark_min

let time_mark_sorted_all (evs: events 'c): prop =
  forall (i j: event_index evs).
    i <= j ==>
    time_mark_sorted evs i j

(* Adequate time gap between events enabled on same cycle *)
let adequate_spacing (evs: events 'c) (c: 'c) (i j: event_index evs): prop =
  i <= j             ==>
  (evs.read i).enabled c ==>
  (evs.read j).enabled c ==>
  (evs.read j).time_mark_min - (evs.read i).time_mark_max >= (j - i) * evs.exec_period

let adequate_spacing_all (evs: events 'c): prop =
  forall (c: 'c). forall (i j: event_index evs).
    adequate_spacing evs c i j

(* Adequate time gap from start of array to trigger:
  a trigger at index `i` must start after the `i`th frame
 *)
let time_mark_reachable (evs: events 'c) (i: event_index evs): prop =
    i * evs.exec_period + evs.exec_period <= (evs.read i).time_mark_min

let time_mark_reachable_all (evs: events 'c): prop =
  forall (i: event_index evs).
    time_mark_reachable evs i

let events_valid_req (evs: events 'c): prop =
  time_mark_sorted_all    evs /\
  adequate_spacing_all    evs /\
  time_mark_reachable_all evs /\
  evs.count > 0

type events_valid 'c = evs: events 'c { events_valid_req evs }

(* we must execute at least once every exec_period - so the new time cannot skip too far *)
let time_period_advances (evs: events 'c) (time time': nat): bool =
  time  <  time' &&
  time' <= time + evs.exec_period

(* True if trigger's time-mark would start before the end of this frame, or has
  already started. Does not check whether trigger is enabled or not.  *)
let time_mark_started (evs: events 'c) (now time_mark: nat): bool =
  time_mark <= now + evs.exec_period

(* True if trigger's time-mark would start in this frame. Does not check
  whether trigger is enabled or not. *)
let time_mark_impending (evs: events 'c) (now time_mark: nat): bool =
  now < time_mark &&
  time_mark <= now + evs.exec_period

let event_enabled_started (evs: events 'c) (c: 'c) (now: nat) (index: event_index evs): bool =
  let ev = evs.read index in
  ev.enabled c && time_mark_started evs now (ev.time_mark c)

(* Check that there are no started and enabled triggers inside the given range *)
let none_started (evs: events 'c) (c: 'c) (now: nat) (begin_ end_: int): prop =
  forall (i: event_index evs { begin_ <= i /\ i < end_ }).
    let ev = evs.read i in
    ev.enabled c ==> not (time_mark_started evs now (ev.time_mark c))

(* Check that all enabled triggers in the range have started *)
let all_started (evs: events 'c) (c: 'c) (now: nat) (begin_ end_: int): prop =
  forall (i: event_index evs { begin_ <= i /\ i < end_ }).
    let ev = evs.read i in
    ev.enabled c ==> time_mark_started evs now (ev.time_mark c)

let lemma_all_started_before (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index evs)
  : Lemma
    (requires (
      time_mark_started evs now ((evs.read index).time_mark c)
    ))
    (ensures (
      all_started evs c now 0 (index + 1)
    ))
    =
  assert (time_mark_sorted_all evs);
  assert (forall (i: event_index evs { i <= index }). time_mark_sorted evs i index);
  assert (forall (i: event_index evs { i <= index }). time_mark_started evs now ((evs.read i).time_mark c));
  assert (all_started evs c now 0 (index + 1));
  ()

let lemma_none_started_after (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index evs)
  : Lemma
    (requires (
      not (time_mark_started evs now ((evs.read index).time_mark c))
    ))
    (ensures (
      none_started evs c now index evs.count
    ))
    =
  assert (time_mark_sorted_all evs);
  assert (forall (i: event_index evs { index <= i }). time_mark_sorted evs index i);
  assert (forall (i: event_index evs { index <= i }). not (time_mark_started evs now ((evs.read i).time_mark c)));
  assert (none_started evs c now index evs.count);
  ()


let maximum_started_spec (evs: events_valid 'c) (c: 'c) (now: nat) (cur: option (event_index evs))
  : prop =
  match cur with
  | Some cur ->
    all_started  evs c now   0 (cur + 1) /\
    none_started evs c now (cur + 1) evs.count /\
    (evs.read cur).enabled c
  | None ->
    none_started evs c now 0 evs.count

let minimum_not_started_spec (evs: events_valid 'c) (c: 'c) (now: nat)  (cur: option (event_index evs))
  : prop =
  match cur with
  | Some cur ->
    all_started  evs c now 0   cur /\
    none_started evs c now cur evs.count /\
    (evs.read cur).enabled c
  | None ->
    all_started evs c now 0 evs.count

(* Compute the currently-active index for given time (specification only).
  We want to find the last index that has actually occurred. To do this, we
  find the next index, and check if that's in the future.

  This function isn't immediately correct on its own. We really
  need to prove something about it, like that it computes:
  > maximum i. enabled i /\ (for n in next i. enabled n /\ time_mark n > time)
*)
let rec maximum_started (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index evs { none_started evs c now (index + 1) evs.count })
  : Tot
    (cur: option (event_index evs) {
      maximum_started_spec evs c now cur
    })
    (decreases index) =
  let ev = evs.read index in
  if ev.enabled c && time_mark_started evs now (ev.time_mark c)
  then begin
    lemma_all_started_before evs c now index;
    Some index
  end
  else if index > 0
  then begin
    maximum_started evs c now (index - 1)
  end
  else None

(* Compute the next-active index for given time (specification only).
*)
let rec minimum_not_started (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index evs { all_started evs c now 0 index })
  : Tot
    (cur: option (event_index evs) {
      minimum_not_started_spec evs c now cur
    })
    (decreases (evs.count - index)) =
  let ev = evs.read index in
  if ev.enabled c && not (time_mark_started evs now (ev.time_mark c))
  then begin
    lemma_none_started_after evs c now index;
    Some index
  end
  else if index < evs.count - 1
  then begin
    minimum_not_started evs c now (index + 1)
  end
  else None

let current (evs: events_valid 'c) (c: 'c) (now: nat)
  : option (event_index evs) =
  maximum_started evs c now (evs.count - 1)

let next (evs: events_valid 'c) (c: 'c) (now: nat)
  : option (event_index evs) =
  minimum_not_started evs c now 0

let prefetch_invariant_can_reach_next (evs: events_valid 'c) (c: 'c) (now: nat) (index nxt: event_index evs): bool =
  let ev = evs.read nxt in
  let tm = ev.time_mark c in
  (nxt - index) * evs.exec_period <= tm - now

let prefetch_invariant (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index evs): bool =
  (match current evs c now with
    | Some cur -> cur <= index
    | None     -> true) &&
  (match next evs c now with
    | Some nxt ->
      index <= nxt &&
      prefetch_invariant_can_reach_next evs c now index nxt
    | None     -> true)

let lemma_current_reset (evs: events_valid 'c) (c: 'c) (now: nat)
  : Lemma
    (requires (
      now < evs.exec_period
    ))
    (ensures (
      match current evs c now with
      | Some cur -> cur = 0
      | None     -> true
    ))
    =
  match current evs c now with
  | Some cur ->
    ()
  | None ->
    ()

let lemma_prefetch_invariant_can_reach_next_reset
  (evs: events_valid 'c) (c: 'c) (now: nat) (next: event_index evs)
  : Lemma
    (requires (
       now < evs.exec_period
    ))
    (ensures (
      prefetch_invariant_can_reach_next evs c now 0 next
    )) =
  ()

let lemma_prefetch_invariant_reset
  (evs: events_valid 'c) (c: 'c) (now: nat)
  : Lemma
    (requires (
       now < evs.exec_period
    ))
    (ensures (
       prefetch_invariant evs c now 0
    ))
    =
  lemma_current_reset evs c now;
  match next evs c now with
  | Some nxt ->
    lemma_prefetch_invariant_can_reach_next_reset evs c now nxt
  | None ->
    ()

let rec lemma_minimum_not_started_find
  (evs: events_valid 'c) (c: 'c) (now: nat) (start index next: event_index evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      all_started evs c now 0 start /\
      minimum_not_started evs c now start == Some next /\
      start <= index /\
      index <= next /\
      ev.enabled c /\
      ~ (time_mark_started evs now (ev.time_mark c))
    ))
    (ensures (
       next == index
    ))
    (decreases (evs.count - start))
    =
  let ev = evs.read start in
  if ev.enabled c && not (time_mark_started evs now (ev.time_mark c))
  then begin
    assert (minimum_not_started evs c now start == Some start);
    ()
  end
  else if start < evs.count - 1
  then begin
    assert (start < index);
    assert (minimum_not_started evs c now (start + 1) == Some next);
    lemma_minimum_not_started_find evs c now (start + 1) index next
  end
  else begin
    false_elim ()
  end

let rec lemma_minimum_not_started_time_increase
  (evs: events_valid 'c) (c: 'c) (now now': nat) (start next: event_index evs)
  : Lemma
    (requires (
      time_period_advances evs now now' /\

      all_started evs c now 0 start /\
      minimum_not_started evs c now start == Some next /\

      start <= next /\
      ~ (time_mark_started evs now' ((evs.read next).time_mark c))
    ))
    (ensures (
      minimum_not_started evs c now' start == Some next
    ))
    (decreases (evs.count - start))
    =
  let ev = evs.read start in
  if ev.enabled c && not (time_mark_started evs now (ev.time_mark c))
  then
    ()
  else if start < evs.count - 1
  then
    lemma_minimum_not_started_time_increase evs c now now' (start + 1) next
  else
    false_elim ()

let rec lemma_maximum_started_time_increase_blank
  (evs: events_valid 'c) (c: 'c) (now now': nat) (cur mid next: event_index evs)
  : Lemma
    (requires (
      time_period_advances evs now now' /\

      none_started evs c now  (cur + 1)  evs.count /\
      none_started evs c now' (mid + 1)  evs.count /\
      all_started  evs c now         0   next      /\

      cur < mid  /\
      mid < next /\

      maximum_started evs c now  cur ==
      maximum_started evs c now' cur
    ))
    (ensures (
      maximum_started evs c now  mid ==
      maximum_started evs c now' mid
    ))
    (decreases mid)
    =
  let ev = evs.read mid in
  if ev.enabled c
  then begin
    false_elim ()
  end
  else if cur < mid - 1
  then
    lemma_maximum_started_time_increase_blank evs c now now' cur (mid - 1) next
  else
    ()
