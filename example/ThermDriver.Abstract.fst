module ThermDriver.Abstract

module ST = FStar.HyperStack.ST

module U8  = FStar.UInt8

type sample = U8.t
let sample_invalid: sample = U8.zero

assume val read: unit -> ST.St (option sample)
assume val reset: unit -> ST.St unit
assume val broadcast: option sample -> ST.St unit
assume val sleep_ms: nat -> ST.St unit

let max_age = 10

let rec driver_loop (age: int) (sample: sample): ST.St (_: unit { false }) =
  match read () with
  | Some t ->
    broadcast (Some t);
    driver_loop 0 t
  | None ->
    if age < max_age
    then (broadcast (Some sample))
    else (reset (); broadcast None);
    sleep_ms 1000;
    driver_loop (age + 1) sample

let go () = driver_loop max_age sample_invalid

type stream t = nat -> t

let driver_lift (read_ok: stream bool) (read_sample: stream sample): (stream bool & stream sample) =
  let rec age t =
    if read_ok t
    then 0
    else if t = 0
    then max_age
    else age (t - 1) + 1
  in
  let ok t = age t < max_age in
  let rec sample t =
    if read_ok t
    then read_sample t
    else if t = 0
    then sample_invalid
    else sample (t - 1)
  in
  (ok, sample)

(*
let driver_lift (read_ok: stream bool) (read_sample: stream sample): (stream bool & stream (option sample)) =
  let rec age t =
    if read_ok t
    then 0
    else if t = 0
    then max_age
    else age (t - 1) + 1
  in
  let rec sample t =
    if read_ok t
    then Some (read_sample t)
    else if age t >= max_age || t = 0
    then None
    else sample (t - 1)
  in
  let reset t = None? (sample t)
  in (reset, sample)

*)

let spec (ghost_samples: stream sample) (read_ok: stream bool): prop =
  let (ok, sample) = driver_lift read_ok ghost_samples in
  forall (now: nat).
    ok now ==> (exists (old: nat {old <= now}). sample now = ghost_samples old /\ read_ok old)
    // ok now ==> (exists (age: nat {age < max_age /\ age <= now}). sample now = ghost_samples (now - age) /\ read_ok (now - age))




// assume val fby : 'a -> stream 'a -> stream 'a
// assume val rec' : (stream 'a -> stream 'a) -> stream 'a

let driver_lift' (read_ok: stream bool) (read_sample: stream sample): (stream bool & stream sample) =
  let rec age =
    if read_ok
    then 0
    else fby max_age (age + 1)
  in
  let ok = age < max_age in
  let rec sample =
    if read_ok
    then read_sample
    else fby sample_invalid sample
  in
  (ok, sample)

let current_when (sample: stream 'a) (clock: stream bool) (init: 'a) =
  let rec current =
    if clock
    then sample
    else fby init current
  in current

let spec' (ghost_samples: stream sample) (read_ok: stream bool): prop =
  let (ok, sample) = driver_lift read_ok ghost_samples in
  ok ==> sample = current_when ghost_samples read_ok



type system i a = {
  state: Type0;
  init: state;
  step: i -> state -> (state & a);
}

let current_when'' (zero: 'a): system (bool & 'a) 'a = {
  state = 'a;
  init = zero;
  step = fun i s ->
    let (ck, sample) = i in
    let o = if ck then sample else s in
    (o, o)
}

// let current_when (sample: system i 'a) (ck: system i bool): system i 'a =
// ...

let driver_lift'' (): system (bool & sample) (bool & sample) = {
  state = nat & sample;
  init = (max_age, sample_invalid);
  step = (fun (read_ok, read_sample) (pre_age, pre_sample) ->
    let age = if read_ok then 0 else pre_age + 1 in
    let ok = age < max_age in
    let sample = if read_ok then read_sample else pre_sample in
    (ok, sample));
}

let spec'' (): system (bool & sample) bool =
  let drv = driver_lift'' in
  let cur = current_when'' sample_invalid in
  {
  state = drv.state & cur.state;
  init  = (drv.init, cur.init);
  step  = (fun (read_ok, read_sample) (drv_s, cur_s) ->
    let (drv_s', (drv_ck, drv_sample)) = drv.step (read_ok, read_sample)  in
    let (cur_s', cur_o) = cur.step (read_ok, read_sample)  in
    ((drv_s', cur_s'), (if drv_ck then drv_sample = cur_o else true))
  ) }
