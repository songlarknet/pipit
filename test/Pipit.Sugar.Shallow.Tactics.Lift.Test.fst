module Pipit.Sugar.Shallow.Tactics.Lift.Test

open Pipit.Sugar.Shallow.Tactics.Lift

module Shallow = Pipit.Sugar.Shallow.Base

module List = FStar.List.Tot

module Tac = FStar.Tactics

#push-options "--print_implicits --print_bound_var_types"
#push-options "--print_universes"
// #push-options "--print_implicits --print_full_names --ugly --print_bound_var_types"

instance has_stream_int: Shallow.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

(*** Examples / test cases ***)

module Tbl = Pipit.Prim.Table

#push-options "--ext pipit:lift:debug=1"
(*

[@@source]
let eg_letincs (x: stream int) =
  (x + x) + x

%splice[] (autolift_binds [`%eg_letincs])

[@@source]
let eg_letincs_ann (x: stream int): stream int =
  (x + x) + x

%splice[] (autolift_binds [`%eg_letincs_ann])

[@@source]
let eg_fby (x: stream int): stream int =
  0 `fby` x

%splice[] (autolift_binds [`%eg_fby])

[@@source]
let eg_fby_inc (x: stream int): stream int =
  0 `fby` x + 1

%splice[] (autolift_binds [`%eg_fby_inc])

[@@source]
let eg_letrecfun (x: int): int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0

%splice[] (autolift_binds [`%eg_letrecfun])

[@@source]
let eg_letrecfun_ann (x: int): int =
  let rec count (x: int): int = if x > 0 then count (x - 1) else 0 in
  count 0

%splice[] (autolift_binds [`%eg_letrecfun_ann])
*)

// TODO!
// [@@Tac.preprocess_with preprocess; source]
// let eg_let (x: stream int): stream int =
  // let strm = x + 1 in
  // strm
// 
// %splice[] (autolift_binds [`%eg_let])

(*
[@@Tac.preprocess_with preprocess; source]
let eg_let_ann (x: stream int): stream int =
  let strm: stream int = x + 1 in
  strm

%splice[] (autolift_binds [`%eg_let_ann])

[@@Tac.preprocess_with preprocess; source]
let eg_letrec (x: stream int): stream int =
  let rec count = 0 `fby` count + 1 in
  count

%splice[] (autolift_binds [`%eg_letrec])

[@@Tac.preprocess_with preprocess; source]
let eg_mixed_ann (x: stream int): stream int =
  let rec count1 = 0 `fby` count1 + 1 in
  let rec count2: stream int = 0 `fby` count2 + 1 in
  let strm1: stream int = 0 in
  let strm2 = 0 <: stream int in
  let strm3 = count1 + strm1 in
  let static1: int = 0 in
  let static2 = 0 in
  count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

%splice[] (autolift_binds [`%eg_mixed_ann])

let eg_pairs (x: stream int) (y: stream bool): stream int =
  // TODO: this requires explicit annotations for now, but it shouldn't really
  0 `fby` fst (Mktuple2 #int #bool x y)

%splice[] (autolift_binds [`%eg_pairs])


type ctor = | Ctor: x: int -> y: int -> ctor
instance has_stream_ctor: Shallow.has_stream ctor = {
  ty_id       = [`%ctor];
  val_default = Ctor Shallow.val_default Shallow.val_default;
}

[@@Tac.preprocess_with preprocess]
let eg_ctor (add: stream int): stream ctor =
  let rec rcd =
    // TODO should not require type annotations
    let x: stream int = 0 `fby` Ctor?.x rcd + add in
    let y: stream int = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

%splice[] (autolift_binds [`%eg_ctor])

[@@Tac.preprocess_with preprocess]
let eg_pairsrec (add: stream int): stream (int & int) =
  let rec xy =
  // TODO rm ann
    let x: stream int = 0 `fby` fst #int #int xy + add in
    let y: stream int = 0 `fby` snd #int #int xy - add in
    Mktuple2 #int #int x y
  in
  xy

%splice[] (autolift_binds [`%eg_pairsrec])

type record = { x: int; y: int; }

instance has_stream_record: Shallow.has_stream record = {
  ty_id       = [`%record];
  val_default = { x = 0; y = 0; };
}


// XXX:TODO: preprocess breaks on records?
// [@@Tac.preprocess_with preprocess]
let eg_record (add: stream int): stream int =
  // TODO rm ann
  let x: stream int = 0 `fby` add in
  let y: stream int = 1 `fby` add in
  let xy: stream record = { x; y } in
  xy.x

%splice[] (autolift_binds [`%eg_record])

*)

// // XXX: not working, why not?
// let eg_streaming_match (x: stream int): stream int =
//   if x >= 0 then x else -x
//   // match x >= 0 with
//   //   | true -> x
//   //   | false -> -x

// %splice[] (autolift_binds [`%eg_streaming_match])

(*
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


*)