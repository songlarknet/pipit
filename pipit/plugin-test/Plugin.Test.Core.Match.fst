module Plugin.Test.Core.Match

open Plugin.Test.Core.Basic

open Pipit.Source
module PPL = Pipit.Plugin.Lift
module PSSB = Pipit.Sugar.Shallow.Base

// Useful for testing:
// #set-options "--ext pipit:lift:debug"
// #set-options "--print_implicits --print_bound_var_types --print_full_names"

[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_if_anf (x: int) =
  let m0 = x >= 0 in
  let m1 = x in
  let m2 = -x in
  if m0 then m1 else m2
%splice[] (PPL.lift_tac1 "eg_streaming_if_anf")

[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_if (x: int) =
  if x >= 0 then x else -x
%splice[] (PPL.lift_tac1 "eg_streaming_if")

[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_match_option (x: option int) =
  match x with
  | None -> -1
  | Some 0 -> 0
  | Some 1 -> 1
  | Some _ -> 2
%splice[] (PPL.lift_tac1 "eg_streaming_match_option")


[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_match_ctor (xy: ctor) =
  let Ctor x y = xy in
  x + y
%splice[] (PPL.lift_tac1 "eg_streaming_match_ctor")

[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_match_rcd (xy: ctor) =
  let {x; y} = xy in
  x + y
%splice[] (PPL.lift_tac1 "eg_streaming_match_rcd")

[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_match_tup (xy: (int & int)) =
  let (x, y) = xy in
  x + y
%splice[] (PPL.lift_tac1 "eg_streaming_match_tup")

// [@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
// let eg_pairs_destr (x: int) (y: bool): int =
//   let xy = (x, y) in
//   let (xz, yz) = xy in
//   0 `fby` xz

// %splice[] (PPL.lift_tac1 "eg_pairs_destr")

// not supported yet, issue proving termination on the generated core
// [@@source_mode (ModeFun Static true (ModeFun Stream true Stream))]
// let rec eg_fir (consts: list int) (x: int): Tot int (decreases consts)
//  =
//   match consts with
//   | [] -> 0
//   | (c: int) :: cs ->
//     let open FStar.Mul in
//     // hmm, explicit type app needed to avoid type inference weirdness
//     let pre: int = 0 `fby` x in
//     c * x + eg_fir cs pre

// %splice[] (PPL.lift_tac1 "eg_fir")

(*** Not supported examples ***)


// streaming matches cannot bind variables:

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match x with
//   | Some e -> e
//   | None -> 0
