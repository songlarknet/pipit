module Plugin.Test.CoreLift

open Pipit.Plugin.Interface
open Pipit.Plugin.Primitives
module PPL = Pipit.Plugin.Lift
module PSSB = Pipit.Sugar.Shallow.Base

// Don't warn on local let-recs; they're only for testing
// #set-options "--warn_error -242"

// Useful for testing:
// #set-options "--ext pipit:lift:debug"
#set-options "--print_implicits --print_bound_var_types --print_full_names"

instance has_stream_int: Pipit.Sugar.Shallow.Base.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

instance has_stream_option (#a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (option a) = {
  ty_id       = `%Pervasives.option :: PSSB.ty_id #a;
  val_default = None;
}

type ctor = | Ctor: x: int -> y: int -> ctor
instance has_stream_ctor: PSSB.has_stream ctor = {
  ty_id       = [`%ctor];
  val_default = Ctor PSSB.val_default PSSB.val_default;
}

type record = { x: int; y: int; }
instance has_stream_record: PSSB.has_stream record = {
  ty_id       = [`%record];
  val_default = { x = 0; y = 0; };
}


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

[@@source_mode (ModeFun Stream true Stream)]
let eg_inc_left_strm (x: int) =
  x + 1

%splice[] (PPL.lift_tac1 "eg_inc_left_strm")

[@@source_mode (ModeFun Stream true Stream)]
let eg_inc_right_strm (x: int) =
  1 + x

%splice[] (PPL.lift_tac1 "eg_inc_right_strm")


[@@source_mode (ModeFun Stream true Stream)]
let eg_additions_strm (x: int) =
  (x + x) + x

%splice[] (PPL.lift_tac1 "eg_additions_strm")

[@@source_mode (ModeFun Stream true Stream)]
let eg_additions_strm_ret_ann (x: int): int =
  (x + x) + x

%splice[] (PPL.lift_tac1 "eg_additions_strm_ret_ann")



[@@source_mode (ModeFun Stream true Stream)]
let eg_fby (x: int) =
  0 `fby` x

%splice[] (PPL.lift_tac1 "eg_fby")


[@@source_mode (ModeFun Stream true Stream)]
let eg_fby_inc (x: int) =
  0 `fby` x + 1

%splice[] (PPL.lift_tac1 "eg_fby_inc")

[@@source_mode (ModeFun Stream true Stream)]
let eg_letrecfun (x: int): int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0

%splice[] (PPL.lift_tac1 "eg_letrecfun")

[@@source_mode (ModeFun Stream true Stream)]
let eg_let_strm (x: int): int =
  let strm = x + 1 in
  strm + x

%splice[] (PPL.lift_tac1 "eg_let_strm")

[@@source_mode (ModeFun Stream true Stream)]
let eg_let_strm_ann (x: int): int =
  [@@source_mode Stream]
  let strm = 1 in
  strm + x

%splice[] (PPL.lift_tac1 "eg_let_strm_ann")

[@@source_mode (ModeFun Stream true Stream)]
let eg_let_stat (x: int): int =
  let stat = 1 in
  x + stat

%splice[] (PPL.lift_tac1 "eg_let_stat")

[@@source_mode (ModeFun Stream true Stream)]
let eg_rec_strm (x: int) =
  let count = rec' (fun count -> 0 `fby` count + 1) in
  count

%splice[] (PPL.lift_tac1 "eg_rec_strm")

[@@source_mode (ModeFun Stream true Stream)]
let eg_rec_strm_let_stat (x: int) =
  let count1 = rec' (fun count1 -> 0 `fby` count1 + 1) in
  let static1: int = 0 in
  count1 + static1

%splice[] (PPL.lift_tac1 "eg_rec_strm_let_stat")

// slow!
[@@source_mode (ModeFun Stream true Stream)]
let eg_mixed_ann (x: int) =
  let count1 = rec' (fun count1 -> 0 `fby` count1 + 1) in
  [@@source_mode Stream]
  let count2 = rec' (fun count2 -> 0 `fby` count2 + 1) in
  [@@source_mode Stream]
  let strm1 = 0 in
  [@@source_mode Stream]
  let strm2: int = 0 in
  let strm3 = count1 + strm1 in
  [@@source_mode Static]
  let static1: int = 0 in
  let static2 = 0 in
  count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

%splice[] (PPL.lift_tac1 "eg_mixed_ann")

[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let eg_pairs (x: int) (y: bool): int =
  0 `fby` fst (x, y)

%splice[] (PPL.lift_tac1 "eg_pairs")

// TODO matches
// [@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
// let eg_pairs_destr (x: int) (y: bool): int =
//   let xy = (x, y) in
//   let (xz, yz) = xy in
//   0 `fby` xz

// %splice[] (PPL.lift_tac1 "eg_pairs_destr")

[@@source_mode (ModeFun Stream true Stream)]
let eg_ctor (add: int) =
  let rcd = rec' (fun rcd ->
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y)
  in
  rcd

%splice[] (PPL.lift_tac1 "eg_ctor")

[@@source_mode (ModeFun Stream true Stream)]
let eg_pairsrec (add: int) =
  let xy = rec' (fun xy ->
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y))
  in
  xy

%splice[] (PPL.lift_tac1 "eg_pairsrec")


[@@source_mode (ModeFun Stream true Stream)]
let eg_record (add: int) =
  let x = 0 `fby` add in
  let y = 1 `fby` add in
  let xy = { x; y } in
  xy.x


%splice[] (PPL.lift_tac1 "eg_record")

[@@source_mode (ModeFun Stream true Stream)]
let eg_streaming_match_lets (x: int): int =
  let cond = x >= 0 in
  let abs =
    match cond with
      | true -> x
      | false -> -x
  in abs

%splice[] (PPL.lift_tac1 "eg_streaming_match_lets")

[@@source_mode (ModeFun Static true (ModeFun Stream true Stream))]
let eg_static_match (consts: list int) (x: int) =
  match consts with
  | [] -> 0
  | (c: int) :: _ -> c + x

%splice[] (PPL.lift_tac1 "eg_static_match")

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

let silly_id (x: int): y: int { x == y } = x

[@@source_mode (ModeFun Stream true Stream)]
let eg_refinement0 (x: int) =
  silly_id x

%splice[] (PPL.lift_tac1 "eg_refinement0")

(*** Not supported examples ***)


// streaming matches cannot bind variables:

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match x with
//   | Some e -> e
//   | None -> 0


// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y

// %splice[] (autolift_binds [`%eg_instantiate_lemma])
