module Network.TTCan.Types.Triggers

open Network.TTCan.Types.Base

module Schedule = Network.TTCan.Abstract.Schedule

module U64        = Network.TTCan.Prim.U64
module Subrange   = Network.TTCan.Prim.S32R

module List       = FStar.List.Tot

module UInt8      = FStar.UInt8
module UInt64     = FStar.UInt64
module Cast       = FStar.Int.Cast

open FStar.Mul

(* We assume a total, safe indexing function for triggers.
  The actual implementation will likely be backed by a read-only array. Since
  we only support at most 64 triggers, it doesn't really hurt to allocate space
  for all 64 of them.
*)
type trigger_index_fun = trigger_index -> trigger

(***** Non-streaming helper functions ****)
let trigger_check_enabled (cycle_index: cycle_index) (trigger: trigger): bool =
  let mask    = Subrange.pow2_minus_one trigger.repeat_factor in
  assert_norm ((Int.pow2_n #8 6 - 1) <= 255);
  let mask8   = Subrange.s32r_to_u8 mask in
  let index8  = Subrange.s32r_to_u8 cycle_index in
  let offset8 = Subrange.s32r_to_u8 trigger.cycle_offset in
  UInt8.logand mask8 index8 = offset8

let trigger_tx_ref_expiry (tx_enable_window: tx_enable_window) (ix: trigger_index) (trigger: trigger): ntu =
  let open UInt64 in
  let tm = Subrange.s32r_to_u64 trigger.time_mark in
  tm +^ Subrange.s32r_to_u64 tx_enable_window

let trigger_offset_time_mark (trigger: trigger) (ref_trigger_offset: ref_offset): ntu_config =
  match trigger.trigger_type with
  | Tx_Ref_Trigger ->
    Subrange.add_sat trigger.time_mark ref_trigger_offset
  | _ ->
    trigger.time_mark

type abstract_cycle = { cycle_index: cycle_index; ref_trigger_offset: ref_offset; }

let abstract_trigger (trigger: trigger): Schedule.event_info abstract_cycle =
  {
    enabled = (fun c -> trigger_check_enabled c.cycle_index trigger);
    time_mark = (fun c -> Subrange.v (trigger_offset_time_mark trigger c.ref_trigger_offset));
    time_mark_min = Subrange.v (trigger_offset_time_mark trigger (Subrange.s32r (-127)));
    time_mark_max = Subrange.v (trigger_offset_time_mark trigger (Subrange.s32r (127)));
    ok = ();
  }

let trigger_min_time_mark (trigger: trigger): ntu_config =
  trigger_offset_time_mark trigger (Subrange.s32r (-127))

let trigger_max_time_mark (trigger: trigger): ntu_config =
  trigger_offset_time_mark trigger (Subrange.s32r 127)

let lemma_trigger_offset_time_mark_range (trigger: trigger) (ref_trigger_offset: ref_offset)
  : Lemma (ensures (
    Subrange.v (trigger_min_time_mark trigger) <=
    Subrange.v (trigger_offset_time_mark trigger ref_trigger_offset) /\
    Subrange.v (trigger_offset_time_mark trigger ref_trigger_offset) <=
    Subrange.v (trigger_max_time_mark trigger)
  )) =
  ()

// let trigger_offsets (trigger_read: trigger_index_fun) (ref_trigger_offset: ref_offset): trigger_index_fun =
//   fun i ->
//     let trigger = trigger_read i in
//     let time_mark = trigger_offset_time_mark trigger ref_trigger_offset in
//     { trigger with time_mark }

(***** Requirements on trigger array ****)

(* Time-marks are sorted *)
let time_mark_sorted_all (trigger_read: trigger_index_fun): prop =
  forall (i: trigger_index).
    Subrange.v (trigger_max_time_mark (trigger_read i)) <=
    Subrange.v (trigger_min_time_mark (trigger_read (Subrange.inc_sat i)))

(* Adequate time gap between triggers enabled on same cycle *)
let adequate_spacing (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config) (c: cycle_index) (i j: trigger_index): prop =
  Subrange.v i <= Subrange.v j             ==>
  trigger_check_enabled c (trigger_read i) ==>
  trigger_check_enabled c (trigger_read j) ==>
  (Subrange.v (trigger_min_time_mark (trigger_read j)) - Subrange.v (trigger_max_time_mark (trigger_read i))) >= (Subrange.v j - Subrange.v i) * Subrange.v ttcan_exec_period

let adequate_spacing_all (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config): prop =
  forall (c: cycle_index). forall (i j: trigger_index).
    adequate_spacing trigger_read ttcan_exec_period c i j

(* Adequate time gap from start of array to trigger:
  a trigger at index `i` must start after the `i`th frame
 *)
let time_mark_reachable (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config) (i: trigger_index): prop =
    Subrange.v i * Subrange.v ttcan_exec_period + Subrange.v ttcan_exec_period <= Subrange.v (trigger_min_time_mark (trigger_read i))

let time_mark_reachable_all (trigger_read: trigger_index_fun) (ttcan_exec_period: ntu_config): prop =
  forall (i: trigger_index).
    time_mark_reachable trigger_read ttcan_exec_period i

(* Trigger configuration: the array as an index function, the period of
  execution frequency (eg once per 10µs), as well as the proofs that the array
  represents a valid schedule. *)
noeq
type triggers = {
  trigger_read: trigger_index_fun;
  ttcan_exec_period: ntu_config;

  time_mark_sorted_all: squash (time_mark_sorted_all trigger_read);
  adequate_spacing_all: squash (adequate_spacing_all trigger_read ttcan_exec_period);
  time_mark_reachable_all: squash (time_mark_reachable_all trigger_read ttcan_exec_period);
}

noextract
let time_within_one_step (triggers: triggers) (time time': ntu): bool =
  UInt64.v time < UInt64.v time' &&
  UInt64.v time' <= UInt64.v time + Subrange.v triggers.ttcan_exec_period

(* True if trigger's time-mark would start before the end of this frame, or has
  already started. Does not check whether trigger is enabled or not.  *)
noextract
let trigger_mark_started (triggers: triggers) (cycle_time: ntu) (offset_time_mark: ntu_config): bool =
  Subrange.v offset_time_mark <= UInt64.v cycle_time + Subrange.v triggers.ttcan_exec_period

(* True if trigger's time-mark would start in this frame. Does not check
  whether trigger is enabled or not. *)
noextract
let trigger_mark_impending (triggers: triggers) (cycle_time: ntu) (offset_time_mark: ntu_config): bool =
  UInt64.v cycle_time < Subrange.v offset_time_mark && Subrange.v offset_time_mark <= UInt64.v cycle_time + Subrange.v triggers.ttcan_exec_period

(* Note Specification Only
  -----------------------
  Many of these functions must not be called as executable code, as they loop
  through the triggers array - but this would have the wrong runtime complexity
  (linear in the number of triggers, rather than constant).
  We mark these functions as noextract so they can't be extracted. Really they
  should be ghost, but Pipit doesn't support ghost code yet.
  *)


(* Check if trigger is enabled and started -- that is, its time-mark is on or before this frame *)
let trigger_enabled_started (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu) (cur: trigger_index): bool =
  let tr = triggers.trigger_read cur in
  trigger_check_enabled cycle_index tr &&
  trigger_mark_started triggers time (trigger_offset_time_mark tr ref_trigger_offset)

(* Check that there are no started and enabled triggers after this one *)
let trigger_none_later (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu) (cur: trigger_index): prop =
  forall (i: trigger_index { Subrange.v cur < Subrange.v i}).
    not (trigger_enabled_started triggers cycle_index ref_trigger_offset time i)

(* Check that all enabled triggers before this one have started *)
let trigger_all_before (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu) (cur: trigger_index): prop =
  forall (i: trigger_index { Subrange.v i < Subrange.v cur }).
    let tr = triggers.trigger_read i in
    trigger_check_enabled cycle_index tr ==>
      trigger_mark_started triggers time (trigger_offset_time_mark tr ref_trigger_offset)

(* Compute the currently-active index for given time (specification only).
  We want to find the last index that has actually occurred. To do this, we
  find the next index, and check if that's in the future.

  This function isn't immediately correct on its own. We really
  need to prove something about it, like that it computes:
  > maximum i. enabled i /\ (for n in next i. enabled n /\ time_mark n > time)
*)
noextract
let rec trigger_last_before (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu)
  (index: trigger_index { trigger_none_later triggers cycle_index ref_trigger_offset time index })
  : Tot
    (cur: option trigger_index {
      Some? cur ==>
        (trigger_enabled_started triggers cycle_index ref_trigger_offset time (Some?.v cur) /\
        trigger_none_later triggers cycle_index ref_trigger_offset time (Some?.v cur))
    })
    (decreases (Subrange.v index)) =
  if trigger_enabled_started triggers cycle_index ref_trigger_offset time index
  then Some index
  else if Subrange.v index > 0
  then begin
    let dec = Subrange.s32r (Subrange.v index - 1) in
    // introduce forall (i: trigger_index { Subrange.v dec < Subrange.v i }). not (trigger_enabled_started triggers cycle_index ref_trigger_offset time i)
    //   with (
    //     if i = index
    //     then ()
    //     else (
    //       eliminate forall (i: trigger_index { Subrange.v index < Subrange.v i }). not (trigger_enabled_started triggers cycle_index ref_trigger_offset time i)
    //       with i
    //     )
    //   );

    trigger_last_before triggers cycle_index ref_trigger_offset time dec
  end
  else None

noextract
let rec trigger_first_after (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu)
  (index: trigger_index { trigger_all_before triggers cycle_index ref_trigger_offset time index })
  : Tot
    (cur: option trigger_index {
      Some? cur ==>
        (trigger_check_enabled cycle_index (triggers.trigger_read (Some?.v cur)) /\
        ~ (trigger_mark_started triggers time (trigger_offset_time_mark (triggers.trigger_read (Some?.v cur)) ref_trigger_offset)) /\
        trigger_all_before triggers cycle_index ref_trigger_offset time (Some?.v cur))
    })
    (decreases (max_trigger_index - Subrange.v index)) =
  let tr = triggers.trigger_read index in
  if trigger_check_enabled cycle_index tr && not (trigger_mark_started triggers time (trigger_offset_time_mark tr ref_trigger_offset))
  then begin
    assert (trigger_check_enabled cycle_index (triggers.trigger_read index));
    assert (~ (trigger_mark_started triggers time (trigger_offset_time_mark (triggers.trigger_read index) ref_trigger_offset)));
    assert (trigger_all_before triggers cycle_index ref_trigger_offset time index);
    Some index
  end
  else if Subrange.v index < max_trigger_index
  then begin
    let inc = Subrange.inc_sat index in
    // TODO ASSUME
    assume (trigger_all_before triggers cycle_index ref_trigger_offset time inc);
    // introduce forall (i: trigger_index { Subrange.v i < Subrange.v inc }). not (trigger_enabled_started triggers cycle_index ref_trigger_offset time i)
    //   with (
    //     if i = index
    //     then ()
    //     else (
    //       eliminate forall (i: trigger_index { Subrange.v index < Subrange.v i }). not (trigger_enabled_started triggers cycle_index ref_trigger_offset time i)
    //       with i
    //     )
    //   );

    trigger_first_after triggers cycle_index ref_trigger_offset time inc
  end
  else None

(* Compute the currently-active trigger for given time (specification only) *)
noextract
let trigger_current (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu)
  : (cur: option trigger_index {
      Some? cur ==>
        (trigger_enabled_started triggers cycle_index ref_trigger_offset time (Some?.v cur) /\
        trigger_none_later triggers cycle_index ref_trigger_offset time (Some?.v cur))
    }) =
  trigger_last_before triggers cycle_index ref_trigger_offset time (Subrange.s32r max_trigger_index)

noextract
let trigger_next (triggers: triggers) (cycle_index: cycle_index) (ref_trigger_offset: ref_offset) (time: ntu)
  : (cur: option trigger_index {
      Some? cur ==>
        (trigger_check_enabled cycle_index (triggers.trigger_read (Some?.v cur)) /\
        ~ (trigger_mark_started triggers time (trigger_offset_time_mark (triggers.trigger_read (Some?.v cur)) ref_trigger_offset)) /\
        trigger_all_before triggers cycle_index ref_trigger_offset time (Some?.v cur))
    }) =
  trigger_first_after triggers cycle_index ref_trigger_offset time (Subrange.s32r 0)

(**** Prefetch invariant ****)

(* The "can reach next" portion of the invariant states that, at a given
  current `index` and current `time`, the driver has enough time to move from
  `index` to the `next` index before the `next` trigger starts.  *)
let trigger_prefetch_invariant_can_reach_next (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu) (index: trigger_index) (next: trigger_index): bool =
    let tr = triggers.trigger_read next in
    let tm = trigger_offset_time_mark tr rto in
    (Subrange.v next - Subrange.v index) * Subrange.v triggers.ttcan_exec_period <= Subrange.v tm - UInt64.v time

(* The prefetch index always points to somewhere between the current-active and
  the next-active trigger.
  If there is no current trigger, 0 <= index.
  If there is no next trigger, index <= max_trigger_count.
  *)

let trigger_prefetch_invariant (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu) (index: trigger_index): bool =
  (match trigger_current triggers c rto time with
    | Some cur ->
      Subrange.v cur <= Subrange.v index
    | _        -> true) &&
  (match trigger_next triggers c rto time with
    | Some nxt ->
      Subrange.v index <= Subrange.v nxt &&
      trigger_prefetch_invariant_can_reach_next triggers c rto time index nxt
    | _        -> true)

let lemma_lt_period_mul (period: nat) (cur: nat) (time: nat)
  : Lemma
    (requires (
      time < period /\ cur * period <= time
    ))
    (ensures (
      cur == 0
    ))
  = ()

let lemma_current_reset
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu)
  : Lemma
    (requires (
      UInt64.v time < Subrange.v triggers.ttcan_exec_period
    ))
    (ensures (
      let cur = trigger_current triggers c rto time in
      cur == Some (Subrange.s32r 0) \/ cur == None
    )) =
  match trigger_current triggers c rto time with
    | Some cur ->
      let tr = triggers.trigger_read cur in
      lemma_trigger_offset_time_mark_range tr rto;
      let tm = trigger_offset_time_mark tr rto in
      assert (time_mark_reachable triggers.trigger_read triggers.ttcan_exec_period cur);
      assert (trigger_enabled_started triggers c rto time cur);
      assert (trigger_mark_started triggers time tm);
      lemma_lt_period_mul (Subrange.v triggers.ttcan_exec_period) (Subrange.v cur) (UInt64.v time);
      ()
    | None ->
      ()

let lemma_prefetch_invariant_can_reach_next_reset
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu) (next: trigger_index)
  : Lemma
    (requires (
       UInt64.v time < Subrange.v triggers.ttcan_exec_period
    ))
    (ensures (
      trigger_prefetch_invariant_can_reach_next triggers c rto time (Subrange.s32r 0) next
    )) =
  // let ix_zero: trigger_index = Subrange.s32r 0 in
  let tr = triggers.trigger_read next in
  // let tm = trigger_offset_time_mark tr rto in
  lemma_trigger_offset_time_mark_range tr rto;
  // assert (time_mark_reachable triggers.trigger_read triggers.ttcan_exec_period next);
  // assert (Subrange.v next == (Subrange.v next - Subrange.v ix_zero));
  // assert (Subrange.v next * Subrange.v triggers.ttcan_exec_period + Subrange.v triggers.ttcan_exec_period <= Subrange.v (trigger_min_time_mark (triggers.trigger_read next)));
  // assert (Subrange.v next * Subrange.v triggers.ttcan_exec_period <= Subrange.v tm - UInt64.v time);
  // assert ((Subrange.v next - Subrange.v ix_zero) * Subrange.v triggers.ttcan_exec_period <= Subrange.v tm - UInt64.v time);
  ()

irreducible
let lemma_prefetch_invariant_reset_pattern
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu)
  = ()

let lemma_prefetch_invariant_reset
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu)
  : Lemma
    (requires (
       UInt64.v time < Subrange.v triggers.ttcan_exec_period
    ))
    (ensures (
       trigger_prefetch_invariant triggers c rto time (Subrange.s32r 0)
    ))
    [SMTPat (lemma_prefetch_invariant_reset_pattern triggers c rto time)]
    =
  lemma_current_reset triggers c rto time;
  match trigger_next triggers c rto time with
  | Some nxt ->
    lemma_prefetch_invariant_can_reach_next_reset triggers c rto time nxt
  | None ->
    ()

let rec lemma_trigger_first_after_find
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu) (start index next: trigger_index)
  : Lemma
    (requires (
      let tr = triggers.trigger_read index in
      trigger_all_before triggers c rto time start /\
      trigger_first_after triggers c rto time start == Some next /\
      Subrange.v start <= Subrange.v index /\
      Subrange.v index <= Subrange.v next /\
      trigger_check_enabled c tr /\
      ~ (trigger_mark_started triggers time (trigger_offset_time_mark tr rto))
    ))
    (ensures (
       next == index
    ))
    (decreases (max_trigger_count - Subrange.v start))
    =
  let trs = triggers.trigger_read start in
  if trigger_check_enabled c trs && not (trigger_mark_started triggers time (trigger_offset_time_mark trs rto))
  then begin
    assert (trigger_first_after triggers c rto time start == Some start);
    assert (next == start);
    assert (Subrange.v start <= Subrange.v index);
    assert (Subrange.v index <= Subrange.v start);
    assert (Subrange.v start == Subrange.v index);
    assert (next == index);
    ()
  end
  else if Subrange.v start < max_trigger_index
  then begin
    assert (Subrange.v start < Subrange.v index);
    assert (trigger_first_after triggers c rto time (Subrange.inc_sat start) == Some next);
    lemma_trigger_first_after_find triggers c rto time (Subrange.inc_sat start) index next
  end
  else begin
    assert (Subrange.v index <= max_trigger_index);
    false_elim ()
  end

let rec lemma_trigger_first_after_time_increase
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time time': ntu) (start next: trigger_index)
  : Lemma
    (requires (
      let tr = triggers.trigger_read next in
      // trigger_prefetch_invariant triggers c rto time index /\
      time_within_one_step triggers time time' /\

      trigger_all_before triggers c rto time start /\
      trigger_first_after triggers c rto time start == Some next /\

      Subrange.v start <= Subrange.v next /\

      ~ (trigger_mark_started triggers time' (trigger_offset_time_mark tr rto))
    ))
    (ensures (
      trigger_first_after triggers c rto time' start == Some next
    ))
    (decreases (max_trigger_count - Subrange.v start))
    =
  let trs = triggers.trigger_read start in
  if trigger_check_enabled c trs && not (trigger_mark_started triggers time (trigger_offset_time_mark trs rto))
  then begin
    assert (trigger_first_after triggers c rto time start == Some start);
    assert (trigger_first_after triggers c rto time' start == Some start);
    ()
  end
  else if Subrange.v start < max_trigger_index
  then begin
    assert (Subrange.v start < Subrange.v next);
    assert (trigger_first_after triggers c rto time (Subrange.inc_sat start) == Some next);
    lemma_trigger_first_after_time_increase triggers c rto time time' (Subrange.inc_sat start) next
  end
  else begin
    false_elim ()
  end

let lemma_trigger_index_lt_ge_dec_eq (cur mid: trigger_index)
  : Lemma
    (requires (
      Subrange.v cur <  Subrange.v mid /\
      Subrange.v cur >= Subrange.v mid - 1
    ))
    (ensures (
      Subrange.v cur == Subrange.v mid - 1
    ))
  = ()

#push-options "--split_queries always"

let rec lemma_trigger_last_before_time_increase_blank
  (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time time': ntu) (cur mid next: trigger_index)
  : Lemma
    (requires (
      time_within_one_step triggers time time' /\

      trigger_none_later triggers c rto time  cur  /\
      trigger_none_later triggers c rto time' mid  /\
      trigger_all_before triggers c rto time  next /\

      Subrange.v cur < Subrange.v mid  /\
      Subrange.v mid < Subrange.v next /\

      trigger_last_before triggers c rto time  cur  ==
      trigger_last_before triggers c rto time' cur
    ))
    (ensures (
      // trigger_none_later triggers c rto time' mid /\
      trigger_last_before triggers c rto time  mid  ==
      trigger_last_before triggers c rto time' mid
    ))
    (decreases (Subrange.v mid))
    =
  let tr = triggers.trigger_read mid in
  let tm = trigger_offset_time_mark tr rto in
  if trigger_check_enabled c tr
  then begin
    // by trigger_all_before
    assert (trigger_mark_started triggers time tm);
    // by trigger_none_later
    assert (~ (trigger_enabled_started triggers c rto time mid));
    assert (~ (trigger_mark_started triggers time tm));
    false_elim ()
  end
  else if Subrange.v cur < Subrange.v mid - 1
  then begin
    lemma_trigger_last_before_time_increase_blank triggers c rto time time' cur (Subrange.dec_sat mid) next;
    ()
  end
  else begin
    lemma_trigger_index_lt_ge_dec_eq cur mid;
    ()
  end

// let rec lemma_trigger_last_before_time_increase
//   (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time time': ntu) (start next cur: trigger_index)
//   : Lemma
//     (requires (
//       let tr = triggers.trigger_read next in
      // time_within_one_step triggers time time' /\

//       trigger_none_later triggers c rto time' start /\
//       // trigger_last_before triggers c rto time start == Some cur /\
//       // consequence of trigger_last_before
//       trigger_none_later triggers c rto time cur /\

//       Subrange.v cur  <= Subrange.v next  /\
//       Subrange.v next <= Subrange.v start /\

//       trigger_next triggers c rto time  == Some next /\
//       trigger_next triggers c rto time' == Some next /\
//       // trigger_next triggers c rto time  == Some next /\
//       // trigger_next triggers c rto time' == Some next /\
//       // consequence of trigger_next
//       // trigger_all_before triggers c rto time next /\
//       // trigger_all_before triggers c rto time' next /\

//       trigger_check_enabled c tr /\
//       ~ (trigger_mark_started triggers time' (trigger_offset_time_mark tr rto))
//     ))
//     (ensures (
//       trigger_none_later triggers c rto time' cur /\
//       trigger_last_before triggers c rto time  start ==
//       trigger_last_before triggers c rto time' start
//     ))
//     (decreases (Subrange.v start))
//     =
//     admit ()

  // let trs = triggers.trigger_read start in
  // if trigger_check_enabled c trs && not (trigger_mark_started triggers time (trigger_offset_time_mark trs rto))
  // then begin
  //   assert (trigger_first_after triggers c rto time start == Some start);
  //   assert (trigger_first_after triggers c rto time' start == Some start);
  //   ()
  // end
  // else if Subrange.v start < max_trigger_index
  // then begin
  //   assert (Subrange.v start < Subrange.v next);
  //   assert (trigger_first_after triggers c rto time (Subrange.inc_sat start) == Some next);
  //   lemma_trigger_first_after_time_increase triggers c rto time time' (Subrange.inc_sat start) next
  // end
  // else begin
  //   false_elim ()
  // end



// let lemma_trigger_next_by_time_is_index
//   (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time: ntu) (index: trigger_index)
//   : Lemma
//     (requires (
//       let tr = triggers.trigger_read index in
//       trigger_prefetch_invariant triggers c rto time index /\
//       trigger_check_enabled c tr /\
//       ~ (trigger_mark_started triggers time (trigger_offset_time_mark (triggers.trigger_read index) rto))
//     ))
//     (ensures (
//        trigger_next_by_time triggers c rto time == Some index
//     ))
//     =
//     assert (Subrange.v (trigger_current_inc_or_zero triggers c rto time) <= Subrange.v index);
//     match trigger_next_by_time triggers c rto time with
//     | Some next ->
//       assert (Subrange.v index <= Subrange.v next);
//     | None ->

//     ()

// let lemma_prefetch_invariant_next_stay
//   (triggers: triggers) (c: cycle_index) (rto: ref_offset) (time time': ntu) (index: trigger_index)
//   : Lemma
//     (requires (
//       let tr = triggers.trigger_read index in
//              time_within_one_step triggers time time' /\
//       trigger_prefetch_invariant triggers c rto time index /\
//       trigger_check_enabled c tr /\
//       ~ (trigger_mark_started triggers time' (trigger_offset_time_mark (triggers.trigger_read index) rto))
//     ))
//     (ensures (
//        trigger_prefetch_invariant triggers c rto time' index
//     ))
//     // [SMTPat (lemma_prefetch_invariant_reset_pattern triggers c rto time)]
//     =
//   assert (~ (trigger_mark_started triggers time (trigger_offset_time_mark (triggers.trigger_read index) rto)));
//   let tr = triggers.trigger_read index in
//   let cur = match trigger_current triggers c rto time with
//     | Some cur -> cur
//     | _ -> Subrange.s32r 0 in
//   match trigger_next triggers c cur with
//   | Some next ->
//     // assert (next == index);
//     // assert (trigger_current triggers c rto time == trigger_current triggers c rto time');
//     // lemma_trigger_offset_time_mark_range tr rto;
//     admit ()
//   | None ->
//     // false_elim ()
//     admit ()


// irreducible
// let lemma_adequate_spacing_next_inc_pattern (triggers: triggers) (c: cycle_index) (time: ntu) (i: trigger_index) = ()

// let lemma_adequate_spacing_next_inc
//   (triggers: triggers) (c: cycle_index) (time: ntu) (i: trigger_index)
//   : Lemma
//     (ensures (
//        let n = active_next_after_index triggers.trigger_read c (UInt64.v time) (Subrange.v i) in
//        n < max_trigger_count ==>
//        adequate_spacing triggers.trigger_read triggers.ttcan_exec_period i (Subrange.s32r n) c
//     ))
//     [SMTPat (lemma_adequate_spacing_next_inc_pattern triggers c time i)]
//     = ()

// let trigger_index_invariant (cfg: config) (c: cycle) (now: time) (index: index): bool =
//   match next cfg.triggers index c with
//   | None -> true
//   | Some n -> (cfg.triggers.time_mark n - now) >= (n - index)

// let trigger_fetch_guar (cfg: config) (c: cycle) (index: stream int) (now: stream int): stream bool =
//   (index < cfg.triggers.size && trigger_enabled cfg index c) ==> trigger_time_mark cfg index >= now