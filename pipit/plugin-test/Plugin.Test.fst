module Plugin.Test

#lang-pipit

// open Pipit.Source


// let eg_letincs_pure (x: int) =
//   (x + x) + x

// %splice[] (Pipit.Plugin.Interface.lift_tac "eg_letincs" "x_ppt_core" Pipit.Plugin.Interface.Stream)


// let eg_letincs_strm (x: stream int) =
//   (x + x) + x

// %splice[] (Pipit.Source.Support.lift_tac "x" "x_ppt_core")

// let x = 1

(*** Examples / test cases ***)
// let eg_letincs (x: stream int) =
  // (x + x) + x

// %splice[] (Pipit.Source.Support.lift_tac "x" "x_ppt_core")

// let eg_letincs_ann (x: stream int): stream int =
  // (x + x) + x

(*
let eg_fby (x: stream int): stream int =
  0 `fby` x

let eg_fby_inc (x: stream int): stream int =
  0 `fby` x + 1

let eg_letrecfun (x: int): int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0

let eg_letrecfun_ann (x: int): int =
  let rec count (x: int): int = if x > 0 then count (x - 1) else 0 in
  count 0

let eg_let (x: stream int): stream int =
  let strm = x + 1 in
  strm

let eg_let_ann (x: stream int): stream int =
  let strm: stream int = x + 1 in
  strm

let eg_letrec (x: stream int): stream int =
  let rec count = 0 `fby` count + 1 in
  count

let eg_mixed_ann (x: stream int): stream int =
  let rec count1 = 0 `fby` count1 + 1 in
  let rec count2: stream int = 0 `fby` count2 + 1 in
  let strm1: stream int = 0 in
  let strm2 = 0 <: stream int in
  let strm3 = count1 + strm1 in
  let static1: int = 0 in
  let static2 = 0 in
  count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

let eg_pairs (x: stream int) (y: stream bool): stream int =
  0 `fby` fst (Mktuple2 x y)

type ctor = | Ctor: x: int -> y: int -> ctor

instance has_stream_ctor: Shallow.has_stream ctor = {
  ty_id       = [`%ctor];
  val_default = Ctor Shallow.val_default Shallow.val_default;
}

let eg_ctor (add: stream int): stream ctor =
  let rec rcd =
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

let eg_pairsrec (add: stream int): stream (int & int) =
  // recursive streams sometimes need annotations
  let rec xy: stream (int & int) =
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y)
  in
  xy

type record = { x: int; y: int; }

instance has_stream_record: Shallow.has_stream record = {
  ty_id       = [`%record];
  val_default = { x = 0; y = 0; };
}


let eg_record (add: stream int): stream int =
  let x = 0 `fby` add in
  let y = 1 `fby` add in
  let xy = { x; y } in
  xy.x


let eg_streaming_if (x: stream int): stream int =
  if x >= 0 then x else -x

let eg_streaming_match_lets (x: stream int): stream int =
  let cond = x >= 0 in
  let abs =
    match cond with
      | true -> x
      | false -> -x
  in abs

let eg_static_match (consts: list int) (x: stream int): stream int =
  match consts with
  | [] -> 0
  | (c: int) :: _ -> c + x

let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

let eg_instantiate_lemma (x y: stream int): stream int =
  lemma_nat_something x y;
  x + y

(*** Not supported examples ***)


// mutual recursion not supported:

let eg_letrec_mut (x: int): int =
  let rec a = x + b
      and b = x - a
  in a

// streaming matches cannot bind variables:

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match x with
//   | Some e -> e
//   | None -> 0

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_letmatch (xy: stream (int & int)): stream int =
//   let (x, y) = xy in
//   x + y


*)