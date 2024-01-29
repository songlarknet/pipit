module Pipit.Sugar.Shallow.Tactics.Lift.Test

module Lift = Pipit.Sugar.Shallow.Tactics.Lift

open Pipit.Sugar.Shallow.Base

module List = FStar.List.Tot

module Tac = FStar.Tactics

#push-options "--print_implicits --print_bound_var_types"
// #push-options "--print_implicits --print_full_names --ugly --print_bound_var_types"

instance has_stream_int: has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

(*** Examples / test cases ***)

module Tbl = Pipit.Prim.Table



[@@Tac.preprocess_with Lift.tac_lift]
let eg_letincs (x: stream int): stream int =
  (x + x) + x

[@@Tac.preprocess_with Lift.tac_lift]
let eg_fby (x: stream int): stream int =
  0 `fby` x

[@@Tac.preprocess_with Lift.tac_lift]
let eg_fby_inc (x: stream int): stream int =
  0 `fby` x + 1

// local function bindings require explicit type annotations
[@@Tac.preprocess_with Lift.tac_lift]
let eg_letrecfun (x: int): int =
  let rec count (x: int): int = if x > 0 then count (x - 1) else 0 in
  count 0

[@@Tac.preprocess_with Lift.tac_lift]
let eg_letrec (x: stream int): stream int =
  let rec count = 0 `fby` count + 1 in
  let y = (0 <: stream int) in
  (1 + y) + count + x

[@@Tac.preprocess_with Lift.tac_lift]
let eg_pairs (x: stream int) (y: stream bool): stream int =
  // TODO: this requires explicit annotations for now, but it shouldn't really
  0 `fby` fst #int #bool (Mktuple2 #int #bool x y)


type ctor = | Ctor: x: int -> y: int -> ctor
instance has_stream_ctor: has_stream ctor = {
  ty_id       = [`%ctor];
  val_default = Ctor val_default val_default;
}

[@@Tac.preprocess_with Lift.tac_lift]
let eg_ctor (add: stream int): stream ctor =
  let rec rcd =
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

[@@Tac.preprocess_with Lift.tac_lift]
let eg_pairsrec (add: stream int): stream (int & int) =
  let rec xy =
    let x = 0 `fby` fst #int #int xy + add in
    let y = 0 `fby` snd #int #int xy - add in
    Mktuple2 #int #int x y
  in
  xy

[@@Tac.preprocess_with Lift.tac_lift]
let eg_let (x: stream int): stream int =
  let rec count (x: int): int = if x > 0 then count (x - 1) else x in
  // TODO: rough edge: we need this separate definition because the application
  // of count has an unknown type, despite the explicit annotation
  let count': int -> int = count in
  count' x


// XXX: not working, why not?
// [@@Tac.preprocess_with Lift.tac_lift]
// let eg_streaming_match (x: stream int): stream int =
//   match x >= 0 with
//     | true -> x
//     | false -> -x

[@@Tac.preprocess_with Lift.tac_lift]
let eg_streaming_match_lets (x: stream int): stream int =
  let cond: stream bool = x >= 0 in
  let abs =
    match cond with
      | true -> x
      | false -> -x
  in abs

// [@@Tac.preprocess_with Lift.tac_lift]
// let eg_streaming_if (x: stream int): stream int =
//   let abs =
//     if x >= 0 then x else -x
//   in abs


[@@Tac.preprocess_with Lift.tac_lift]
let eg_static_match (consts: list int) (x: stream int): stream int =
  match consts with
  | [] -> 0
  | (c: int) :: _ -> c + x


let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

[@@Tac.preprocess_with Lift.tac_lift]
let eg_instantiate_lemma (x y: stream int): stream int =
  lemma_nat_something x y;
  x + y


(*** Not supported examples ***)


// mutual recursion not supported:

// [@@Tac.preprocess_with tac_lift]
// let eg_letrec_mut (x: int): int =
//   let rec a = x + b
//       and b = x - a
//   in a

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

// should work, but doesn't:
// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bool (x: stream int): stream bool =
//   match x >= 0 with
//     | true -> false
//     | xr -> xr


// fails: cannot typecheck record accessors?

// type record = { x: int; y: int; }
// [@@Tac.preprocess_with tac_lift]
// let eg_record (add: stream int): stream int =
//   let rec rcd =
//     let x = 0 `fby` rcd.x + add in
//     let y = 0 `fby` rcd.y - add in
//     {x; y}
//   in
//   rcd