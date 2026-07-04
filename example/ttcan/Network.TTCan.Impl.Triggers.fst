module Network.TTCan.Impl.Triggers
#lang-pipit

open Pipit.Source
module PSSB  = Pipit.Prim.HasStream

module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Util  = Network.TTCan.Impl.Util

module Clocked  = Network.TTCan.Prim.Clocked
module Schedule = Network.TTCan.Abstract.Schedule

open Network.TTCan.Types

module UInt64 = FStar.UInt64

(* Cycle and time information required by fetch and prefetch *)
type trigger_input = {
  reset_ck:           bool;
  cycle_time:         ntu_config;
  cycle_index:        cycle_index;
  ref_trigger_offset: ref_offset;
}

type time_end_of_frame = S32R.t { min = 0; max = 13072; }

type prefetch_result = {
  index:     trigger_index;
  enabled:   bool;
  time_mark: ntu_config;
}

type fetch_result = {
  current:      prefetch_result;
  trigger_type: trigger_type;
  message_index: can_buffer_id;
}

(* has_stream instances for the records (manual since cfg-aware records aren't liftable yet). *)
instance has_stream_trigger_input: PSSB.has_stream trigger_input = {
  ty_id       = [`%trigger_input];
  val_default = { reset_ck = PSSB.val_default; cycle_time = PSSB.val_default; cycle_index = PSSB.val_default; ref_trigger_offset = PSSB.val_default; };
}

instance has_stream_prefetch_result: PSSB.has_stream prefetch_result = {
  ty_id       = [`%prefetch_result];
  val_default = { enabled = PSSB.val_default; index = PSSB.val_default; time_mark = PSSB.val_default; };
}

instance has_stream_fetch_result: PSSB.has_stream fetch_result = {
  ty_id       = [`%fetch_result];
  val_default = { current = PSSB.val_default; trigger_type = PSSB.val_default; message_index = PSSB.val_default; };
}

(**** Non-streaming helper functions ****)
noextract
let trigger_load_raw (cfg: config) (ix: trigger_index): trigger =
  cfg.triggers.trigger_read ix

noextract
let trigger_load (cfg: config) (ix: trigger_index) (ref_trigger_offset: ref_offset): trigger =
  [@@no_inline_let]
  let base = trigger_load_raw cfg ix in
  let tm   = trigger_offset_time_mark base ref_trigger_offset in
  { base with time_mark = tm }

let is_started_u64 (now: U64.t) (time_mark: ntu_config): bool =
  let open UInt64 in
  S32R.s32r_to_u64 time_mark <=^ now

let is_started (now: time_end_of_frame) (time_mark: ntu_config): bool =
  is_started_u64 (S32R.s32r_to_u64 now) time_mark

let lemma_is_started (cfg: config) (cycle_time: ntu) (time_mark: ntu_config)
  : Lemma (ensures (
      is_started_u64 cycle_time time_mark ==
      (S32R.v time_mark <= UInt64.v cycle_time)
  )) = ()

let trigger_absolute_time
  (local_time: ntu)
  (cycle_time: ntu)
  (time_mark:  ntu_config)
             : ntu =
  let open UInt64 in
  let time_mark  = S32R.s32r_to_u64 time_mark in
  let diff       = time_mark -%^ cycle_time in
  let diff_mark  = local_time +%^ diff in
  diff_mark

let prefetch_index (reset_ck: bool) (advance: bool) (pre_index: trigger_index): trigger_index =
  if reset_ck
  then S32R.s32r 0
  else if advance
  then S32R.inc_sat pre_index
  else pre_index

(* Streaming validity check. Demonstrates partial-application of the
   static [cfg] arg to [Util.cycle_time_valid]. *)
let trigger_input_valid (cfg: config) (inp: stream trigger_input): stream bool =
  Util.cycle_time_valid cfg inp.reset_ck (S32R.s32r_to_u64 inp.cycle_time) &&
  Util.is_sampled_on #cycle_index inp.cycle_index        inp.reset_ck &&
  Util.is_sampled_on #ref_offset  inp.ref_trigger_offset inp.reset_ck

(*
  Pre-fetch the next enabled trigger.
*)
let prefetch
  (cfg: config)
  (input: stream trigger_input)
    : stream prefetch_result =
  rec' (fun fetch ->
    let pre_index: stream trigger_index = (S32R.s32r 0 <: trigger_index) `fby` fetch.index in
    let advance: stream bool = false `fby` (not fetch.enabled || U64.(S32R.s32r_to_u64 fetch.time_mark <= S32R.s32r_to_u64 input.cycle_time)) in
    let index: stream trigger_index =
      prefetch_index input.reset_ck advance pre_index in
    let trigger = trigger_load cfg index input.ref_trigger_offset in
    let enabled = trigger_check_enabled input.cycle_index trigger in
    { index; enabled; time_mark = trigger.time_mark })

let prefetch_rely
  (cfg: config)
  (input: stream trigger_input)
    : stream bool =
  trigger_input_valid cfg input

(*
  Fetch the current trigger, or the next one if there is no current trigger.
*)
let fetch
  (cfg: config)
  (input: stream trigger_input)
    : stream fetch_result =
  let next: stream prefetch_result =
    prefetch cfg input in
  let take_next: stream bool =
    input.reset_ck || (next.enabled && is_started_u64 (S32R.s32r_to_u64 input.cycle_time) next.time_mark) in
  let rec current =
    if (if true `fby` false then true else take_next) then next else Util.pre current in
  let trigger = trigger_load cfg current.index input.ref_trigger_offset in
  { current; trigger_type = trigger.trigger_type; message_index = trigger.message_index; }


