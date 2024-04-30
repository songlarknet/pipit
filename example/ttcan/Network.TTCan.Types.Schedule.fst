(* Abstract scheduler proofs *)
module Network.TTCan.Types.Schedule

module List       = FStar.List.Tot

open FStar.Mul

#push-options "--fuel 1 --ifuel 1"

(*
  Events are parameterised by abstract "cycle parameters". In the concrete
  system, the cycle parameters contain the currently-active cycle (the cycle
  index) and the current ref-trigger-offset, which denotes the time offset for
  reference messages.
  Cycle parameters are generally denoted by `c` with type parameter `'c`.
*)

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

let event_index_t (evs: events 'c) = n: nat { n <  evs.count }
let event_count_t (evs: events 'c) = n: nat { n <= evs.count }

(***** Requirements on trigger array ****)

(* Time-marks are sorted *)
let time_mark_sorted (evs: events 'c) (i j: event_index_t evs): prop =
  (evs.read i).time_mark_max <= (evs.read j).time_mark_min

let time_mark_sorted_all (evs: events 'c): prop =
  forall (i j: event_index_t evs).
    i <= j ==>
    time_mark_sorted evs i j

(* Adequate time gap between events enabled on same cycle *)
let adequate_spacing (evs: events 'c) (c: 'c) (i j: event_index_t evs): prop =
  i <= j             ==>
  (evs.read i).enabled c ==>
  (evs.read j).enabled c ==>
  (evs.read j).time_mark_min - (evs.read i).time_mark_max >= (j - i) * evs.exec_period

let adequate_spacing_all (evs: events 'c): prop =
  forall (c: 'c). forall (i j: event_index_t evs).
    adequate_spacing evs c i j

(* Adequate time gap from start of array to trigger:
  We must be able to reach a trigger `i` before it starts, so its time mark
  must account for at least (i + 1) steps
  > time_mark(i) : [ (i + 1) * pi, ...)
 *)
let time_mark_reachable (evs: events 'c) (i: event_index_t evs): prop =
    i * evs.exec_period + evs.exec_period <= (evs.read i).time_mark_min

let time_mark_reachable_all (evs: events 'c): prop =
  forall (i: event_index_t evs).
    time_mark_reachable evs i

let events_valid_req (evs: events 'c): prop =
  time_mark_sorted_all    evs /\
  adequate_spacing_all    evs /\
  time_mark_reachable_all evs /\
  evs.count > 0

type events_valid 'c = evs: events 'c { events_valid_req evs }

(* we must execute at least once every exec_period - so the new time cannot skip too far
  > time' : (time, time + pi]
  *)
let time_period_advances (evs: events 'c) (time time': nat): bool =
  time  <  time' &&
  time' <= time + evs.exec_period

(* True if trigger's time-mark would start before the end of this frame, or has
  already started. Does not check whether trigger is enabled or not.
  > started_period : [time_mark - pi, ...)
  *)
let time_mark_started (evs: events 'c) (now time_mark: nat): bool =
  now >= time_mark // - evs.exec_period

(* True if trigger's time-mark would start in this frame. Does not check
  whether trigger is enabled or not.
  > impending_period : [time_mark - pi, time_mark)
  *)
let time_mark_impending (evs: events 'c) (now time_mark: nat): bool =
  time_mark_started evs now time_mark &&
  now <  time_mark + evs.exec_period

let event_enabled_started (evs: events 'c) (c: 'c) (now: nat) (index: event_index_t evs): bool =
  let ev = evs.read index in
  ev.enabled c && time_mark_started evs now (ev.time_mark c)

(* Check that there are no enabled triggers inside the given range *)
let none_enabled (evs: events 'c) (c: 'c) (now: nat) (begin_ end_: int): prop =
  forall (i: event_index_t evs { begin_ <= i /\ i < end_ }).
    not ((evs.read i).enabled c)

(* Check that there are no started and enabled triggers inside the given range *)
let none_started (evs: events 'c) (c: 'c) (now: nat) (begin_ end_: int): prop =
  forall (i: event_index_t evs { begin_ <= i /\ i < end_ }).
    let ev = evs.read i in
    ev.enabled c ==> not (time_mark_started evs now (ev.time_mark c))

(* Check that all enabled triggers in the range have started *)
let all_started (evs: events 'c) (c: 'c) (now: nat) (begin_ end_: int): prop =
  forall (i: event_index_t evs { begin_ <= i /\ i < end_ }).
    let ev = evs.read i in
    ev.enabled c ==> time_mark_started evs now (ev.time_mark c)

let lemma_all_started_before (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index_t evs)
  : Lemma
    (requires (
      time_mark_started evs now ((evs.read index).time_mark c)
    ))
    (ensures (
      all_started evs c now 0 (index + 1)
    ))
    =
  assert (time_mark_sorted_all evs);
  assert (forall (i: event_index_t evs { i <= index }). time_mark_sorted evs i index);
  assert (forall (i: event_index_t evs { i <= index }). time_mark_started evs now ((evs.read i).time_mark c));
  assert (all_started evs c now 0 (index + 1));
  ()

let lemma_none_started_after (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index_t evs)
  : Lemma
    (requires (
      not (time_mark_started evs now ((evs.read index).time_mark c))
    ))
    (ensures (
      none_started evs c now index evs.count
    ))
    =
  assert (time_mark_sorted_all evs);
  assert (forall (i: event_index_t evs { index <= i }). time_mark_sorted evs index i);
  assert (forall (i: event_index_t evs { index <= i }). not (time_mark_started evs now ((evs.read i).time_mark c)));
  assert (none_started evs c now index evs.count);
  ()

let range_begin_of_option (#evs: events_valid 'c) (nxt: option (event_index_t evs)): event_count_t evs =
  match nxt with
  | Some nxt -> nxt + 1
  | None     -> 0

let range_end_of_option (#evs: events_valid 'c) (cur: option (event_index_t evs)): event_count_t evs =
  match cur with
  | Some cur -> cur
  | None     -> evs.count


let maximum_started_spec (evs: events_valid 'c) (c: 'c) (now: nat) (cur: option (event_index_t evs))
  : prop =
  all_started  evs c now 0 (range_begin_of_option cur)           /\
  none_started evs c now   (range_begin_of_option cur) evs.count /\
  (match cur with
  | Some cur -> (evs.read cur).enabled c
  | None     -> true)

let minimum_not_started_spec (evs: events_valid 'c) (c: 'c) (now: nat)  (cur: option (event_index_t evs))
  : prop =
  all_started  evs c now 0 (range_end_of_option cur)           /\
  none_started evs c now   (range_end_of_option cur) evs.count /\
  (match cur with
  | Some cur -> (evs.read cur).enabled c
  | None     -> true)

(* Compute the currently-active index for given time.
  This finds the maximum (latest) index that has already started.
*)
let rec maximum_started (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index_t evs { none_started evs c now (index + 1) evs.count })
  : Tot
    (cur: option (event_index_t evs) {
      maximum_started_spec evs c now cur
    })
    (decreases index) =
  if event_enabled_started evs c now index
  then begin
    lemma_all_started_before evs c now index;
    Some index
  end
  else if index > 0
  then begin
    maximum_started evs c now (index - 1)
  end
  else None

(* Compute the next-active index for given time.
  This finds the minimum (earliest) index that has is enabled, but not yet
  started.
*)
let rec minimum_not_started (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index_t evs { all_started evs c now 0 index })
  : Tot
    (cur: option (event_index_t evs) {
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

(* Compute the currently-active event. *)
let current (evs: events_valid 'c) (c: 'c) (now: nat)
  : option (event_index_t evs) =
  maximum_started evs c now (evs.count - 1)

(* Compute the next-active event. *)
let next (evs: events_valid 'c) (c: 'c) (now: nat)
  : option (event_index_t evs) =
  minimum_not_started evs c now 0

let lemma_none_enabled_between
  (evs: events_valid 'c) (c: 'c) (now: nat)
  : Lemma
    (ensures (
      let begin_ = range_begin_of_option (current evs c now) in
      let end_   = range_end_of_option   (next    evs c now) in
      none_enabled evs c now begin_ end_
    ))
    =
  ()

let prefetch_invariant_can_reach_next (evs: events_valid 'c) (c: 'c) (now: nat) (index nxt: event_index_t evs): bool =
  // let ev = evs.read nxt in
  // let tm = ev.time_mark c in

  // need to arrive at time-mark a touch early
  // let tm_early = tm - 1 in
  // steps required to get from current index to next
  // let steps = nxt - index in
  (nxt - index) * evs.exec_period < (evs.read nxt).time_mark c - now

let prefetch_invariant (evs: events_valid 'c) (c: 'c) (now: nat) (index: event_index_t evs): bool =
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
  (evs: events_valid 'c) (c: 'c) (now: nat) (next: event_index_t evs)
  : Lemma
    (requires (
       now < evs.exec_period
    ))
    (ensures (
      prefetch_invariant_can_reach_next evs c now 0 next
    )) =
  ()

(* Prefetch invariant: reset
  When the time and index are reset, the invariant is established.
*)
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

(*
  When computing the next not-started event, if:
  (NXT) we find a result (next ... == Some nxt);
  (EN) and we know that there is an index `index` that is enabled and not-started;
  (BND) and the index `index` is less than or equal to `nxt`;

  then, the next index `nxt` must actually refer to `index`
*)
let lemma_next_find
  (evs: events_valid 'c) (c: 'c) (now: nat) (index nxt: event_index_t evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      // (NXT)
      next evs c now == Some nxt /\
      // (EN)
      ev.enabled c /\
      ~ (time_mark_started evs now (ev.time_mark c)) /\
      // (BND)
      index <= nxt
    ))
    (ensures (
       nxt == index
    ))
    =
  ()


(*
  When computing the next not-started event, if:
  (TIME) time progresses from now to now' at <=exec_period per tick;
  (NXT) we previously found the next event (next ... now == Some `nxt`);
  (STARTED) and the event is still not started at the updated time now'

  then, the next index remains the same at the updated time now'
*)
let lemma_next_time_increase
  (evs: events_valid 'c) (c: 'c) (now now': nat) (nxt: event_index_t evs)
  : Lemma
    (requires (
      // (TIME)
      time_period_advances evs now now' /\
      // (NXT)
      next evs c now == Some nxt /\
      // (STARTED)
      ~ (time_mark_started evs now' ((evs.read nxt).time_mark c))
    ))
    (ensures (
      next evs c now' == Some nxt
    ))
    =
  ()

(*
  When computing the current started event, if:
  (TIME) time moves forward from now to now';
  (NXT) the next not-yet-started event has not changed;

  then, the current index remains the same at the updated time now'
*)
let lemma_current_time_increase_next_same
  (evs: events_valid 'c) (c: 'c) (now now': nat)
  : Lemma
    (requires (
      // (TIME)
      now <= now' /\
      // (NXT)
      next evs c now  ==
      next evs c now'
    ))
    (ensures (
      current evs c now  ==
      current evs c now'
    ))
    =
  ()

(* Prefetch invariant maintained: stay
  When the current index points to an active / enabled event which has not yet
  started, the prefetch invariant is maintained and the current index remains
  the same.
  *)
let lemma_prefetch_invariant_stay
  (evs: events_valid 'c) (c: 'c) (now now': nat) (index: event_index_t evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      time_period_advances evs now now' /\

      ev.enabled c /\
      ~ (time_mark_started evs now' (ev.time_mark c)) /\

      prefetch_invariant evs c now  index
    ))
    (ensures (
      prefetch_invariant evs c now' index
    ))
  = ()

let lemma_prefetch_invariant_can_reach_next_skip_same
  (evs: events_valid 'c) (c: 'c) (now now': nat)
  (index nxt: event_index_t evs)
  : Lemma
    (requires (
      prefetch_invariant_can_reach_next evs c now index nxt /\
      next evs c now == Some nxt /\
      time_period_advances evs now now' /\
      index < nxt
    ))
    (ensures (
      next evs c now' == Some nxt
      // let ev = evs.read nxt in
      // let tm = ev.time_mark c in
      // ~ (time_mark_started evs now' tm)
    ))
  =
    let ev = evs.read nxt in
    let tm = ev.time_mark c in
    assert (~ (time_mark_started evs now  tm));
    assert (~ (time_mark_started evs now' tm));
    ()

(* Prefetch invariant: skipping disabled preserves next
  If the current event is disabled and time passes, then the new next is the
  same as the old next.
  *)
let lemma_prefetch_invariant_next_time_increase_same
  (evs: events_valid 'c) (c: 'c) (now now': nat) (index: event_index_t evs)
  : Lemma
    (requires (
      time_period_advances evs now now' /\
      not ((evs.read index).enabled c) /\
      prefetch_invariant evs c now  index
    ))
    (ensures (
      next evs c now == next evs c now'
    ))
    =
  match next evs c now with
  | Some nxt ->
    lemma_prefetch_invariant_can_reach_next_skip_same evs c now now' index nxt;
    ()
  | None ->
    ()

let lemma_prefetch_invariant_skip
  (evs: events_valid 'c) (c: 'c) (now now': nat) (index: event_index_t evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      time_period_advances evs now now' /\

      index < evs.count - 1 /\
      not (ev.enabled c) /\

      prefetch_invariant evs c now  index
    ))
    (ensures (
      prefetch_invariant evs c now' (index + 1)
    ))
  =
  lemma_prefetch_invariant_next_time_increase_same evs c now now' index;
  assert (next evs c now    == next evs c now');
  assert (current evs c now == current evs c now');
  ()

let lemma_enabled_time_lt
  (evs: events_valid 'c) (c: 'c)
  (index: event_index_t evs)
  (i: event_index_t evs { index < i })
  : Lemma
    (requires (
      (evs.read index).enabled c /\
      (evs.read i).enabled c
    ))
    (ensures (
      (evs.read index).time_mark c < (evs.read i).time_mark c
    ))
    =
  assert (time_mark_sorted evs index i);
  assert (adequate_spacing evs c index i);
  ()

let lemma_time_mark_both_enabled_gap
  (evs: events_valid 'c) (c: 'c) (now now': nat)
  (i i': event_index_t evs)
  : Lemma
    (requires (
      i < i'
    ))
    (ensures (
      (evs.read i).enabled c ==>
      (evs.read i').enabled c ==>
      ((evs.read i).time_mark c + evs.exec_period <= (evs.read i').time_mark c)
    ))
    =
  assert (time_mark_sorted evs i i');
  assert (adequate_spacing evs c i i');
  ()

let lemma_current_time_increase_start
  (evs: events_valid 'c) (c: 'c) (now now': nat)
  (index: event_index_t evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      time_period_advances evs now now' /\
      ev.enabled c /\
      ~ (time_mark_started evs now (ev.time_mark c)) /\
      time_mark_started evs now' (ev.time_mark c)
    ))
    (ensures (
      current evs c now' == Some index
    ))
    =
  let ev = evs.read index in
  let tm = ev.time_mark c in
  match current evs c now' with
  | Some cur ->
    assert (all_started evs c now' 0 cur);
    assert (none_started evs c now' (cur + 1) evs.count);
    assert (index <= cur);
    introduce forall (i: event_index_t evs { index < i }). (evs.read i).enabled c ==> ~ (time_mark_started evs now' ((evs.read i).time_mark c))
    with begin
      lemma_time_mark_both_enabled_gap evs c now now' index i;
      // assert (time_mark_sorted evs index i);
      // assert (adequate_spacing evs c index i);
      // assert (tm <= (evs.read i).time_mark c);
      // assert ((evs.read i).enabled c ==> tm < ((evs.read i).time_mark c));
      // assume ((evs.read i).enabled c ==> tm + evs.exec_period <= ((evs.read i).time_mark c));
      // FLAKY
      // assert (~ (now >= tm));
      // assert ((now' >= tm));
      // assert (~ (now >= (evs.read i).time_mark c));
      // assert ((evs.read i).enabled c ==> (tm < (evs.read i).time_mark c));
      // assert ((evs.read i).enabled c ==> ~ (now' >= (evs.read i).time_mark c));
      // assert ((evs.read i).enabled c ==> ~ (time_mark_started evs now' ((evs.read i).time_mark c)));
      ()
    end;

    // introduce forall (i: event_index_t evs { index < i }).
    // assert (forall (i: event_index_t evs { index < i }). time_mark_sorted evs index i);
    // assert (forall (i: event_index_t evs { index < i }). adequate_spacing evs c index i);
    // assert (forall (i: event_index_t evs { index < i }). tm <= (evs.read i).time_mark c);
    // assert (forall (i: event_index_t evs { index < i }). (evs.read i).enabled c ==> tm < ((evs.read i).time_mark c));
    // // FLAKY
    // assert (not (now >= tm));
    // assert (forall (i: event_index_t evs { index < i }). (evs.read i).enabled c ==> (evs.read i).time_mark c > now);
    // assume (forall (i: event_index_t evs { index < i }). (evs.read i).enabled c ==> ~ (time_mark_started evs now' ((evs.read i).time_mark c)));
    assert (cur == index)
  | None ->
    false_elim ()


let lemma_prefetch_invariant_can_reach_next_time_increase
  (evs: events_valid 'c) (c: 'c) (now now': nat)
  (index nxt': event_index_t evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      time_period_advances evs now now' /\
      ev.enabled c /\
      ~ (time_mark_started evs now (ev.time_mark c)) /\
      time_mark_started evs now' (ev.time_mark c) /\
      prefetch_invariant evs c now index /\
      next evs c now' == Some nxt'
    ))
    (ensures (
      prefetch_invariant_can_reach_next evs c now' (index + 1) nxt'
    ))
    =
  let ei = evs.read index in
  let en = evs.read nxt' in
  let ti = ei.time_mark c in
  let tn = en.time_mark c in
  assert (adequate_spacing evs c index nxt');
  assert (index <= nxt' /\ ei.enabled c /\ en.enabled c);
  assert (en.time_mark_min - ei.time_mark_max >= (nxt' - index) * evs.exec_period);
  assert (en.time_mark_min <= tn);
  assert (ti <= ei.time_mark_max);
  assert (ti < tn);
  assert (tn - ti >= (nxt' - index) * evs.exec_period);
  assert (now < ti);
  assert (ti <= now');
  // FLAKY
  assert ((nxt' - index) * evs.exec_period - evs.exec_period < tn - now');
  // assert ((nxt' - index) * evs.exec_period < tn - now' + evs.exec_period);
  // assert ((nxt' - (index + 1)) * evs.exec_period < tn - now');
  // assert (prefetch_invariant_can_reach_next evs c now' (index + 1) nxt');
  ()

let lemma_prefetch_invariant_done
  (evs: events_valid 'c) (c: 'c) (now now': nat) (index: event_index_t evs)
  : Lemma
    (requires (
      let ev = evs.read index in
      time_period_advances evs now now' /\

      index < evs.count - 1 /\
      ev.enabled c /\
      ~ (time_mark_started evs now (ev.time_mark c)) /\
      time_mark_started evs now' (ev.time_mark c) /\

      prefetch_invariant evs c now  index
    ))
    (ensures (
      prefetch_invariant evs c now' (index + 1)
    ))
  =
  assert (next    evs c now  == Some index);
  lemma_current_time_increase_start evs c now now' index;
  match next evs c now' with
  | Some nxt' ->
    lemma_prefetch_invariant_can_reach_next_time_increase evs c now now' index nxt';
    assert (prefetch_invariant_can_reach_next evs c now' (index + 1) nxt');
    assert (prefetch_invariant evs c now' (index + 1));
    ()
  | None ->
    assert (prefetch_invariant evs c now' (index + 1));
    ()


let lemma_prefetch_invariant_end
  (evs: events_valid 'c) (c: 'c) (now now': nat) (index: event_index_t evs)
  : Lemma
    (requires (
      time_period_advances evs now now' /\
      index == evs.count - 1 /\
      prefetch_invariant evs c now  index
    ))
    (ensures (
      prefetch_invariant evs c now' index
    ))
  =
  ()
