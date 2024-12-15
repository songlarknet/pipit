module Plugin.Test.CoreLift

open Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
module PPI = Pipit.Plugin.Interface

module PXB = Pipit.Exp.Base
module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table

// Don't warn on local let-recs; they're only for testing
#push-options "--warn_error -242"

// Useful for testing:
#push-options "--ext pipit:lift:debug"
#push-options "--print_implicits --print_bound_var_types --print_full_names"

instance has_stream_int: Pipit.Sugar.Shallow.Base.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

// define fby primitive by manually lifting
let fby (#a: eqtype) {| PSSB.has_stream a |} (dflt: a) (strm: a): a = dflt

[@@core_lifted; core_of_source "Plugin.Test.CoreLift.fby" (ModeFun Static false (ModeFun Static false (ModeFun Static true (ModeFun Stream true Stream))))]
let fby_core (ctx: PPT.context PPS.table) (#a: eqtype) {| PSSB.has_stream a |}
  (dflt: a) (strm: PXB.exp PPS.table ctx (PSSB.shallow a)): PXB.exp PPS.table ctx (PSSB.shallow a) =
  PXB.XFby dflt strm

// let rec' (#a: eqtype) {| PSSB.has_stream a |} (f: a -> a): a = admit ()

// rec can't currently be implemented here, because the contexts required for rec are a bit weird
// [@@core_lifted; core_of_source "Plugin.Test.CoreLift.rec'" (ModeFun Static false (ModeFun Static false (ModeFun (ModeFun Stream true Stream) true Stream)))]
// let rec_core (ctx: PPT.context PPS.table) (#a: eqtype) {| PSSB.has_stream a |}
//   (f: PXB.exp PPS.table (PSSB.shallow a :: ctx) (PSSB.shallow a) -> PXB.exp PPS.table (PSSB.shallow a :: ctx) (PSSB.shallow a)): PXB.exp PPS.table ctx (PSSB.shallow a) =
//   PXB.XMu (
//     let x = PXB.XBase (PXB.XBVar 0) in
//     f x)


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
let eg_rec_strm (x: int) =
  let count = rec' (fun count -> 0 `fby` count + 1) in
  count

%splice[] (PPL.lift_tac1 "eg_rec_strm")

// [@@Tac.preprocess_with preprocess; source]
// let eg_mixed_ann (x: stream int): stream int =
//   let rec count1 = 0 `fby` count1 + 1 in
//   let rec count2: stream int = 0 `fby` count2 + 1 in
//   let strm1: stream int = 0 in
//   let strm2 = 0 <: stream int in
//   let strm3 = count1 + strm1 in
//   let static1: int = 0 in
//   let static2 = 0 in
//   count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

// %splice[] (autolift_binds [`%eg_mixed_ann])

// let eg_pairs (x: stream int) (y: stream bool): stream int =
//   0 `fby` fst (Mktuple2 x y)

// %splice[] (autolift_binds [`%eg_pairs])


// type ctor = | Ctor: x: int -> y: int -> ctor
// instance has_stream_ctor: Shallow.has_stream ctor = {
//   ty_id       = [`%ctor];
//   val_default = Ctor Shallow.val_default Shallow.val_default;
// }

// [@@Tac.preprocess_with preprocess]
// let eg_ctor (add: stream int): stream ctor =
//   let rec rcd =
//     let x = 0 `fby` Ctor?.x rcd + add in
//     let y = 0 `fby` Ctor?.y rcd - add in
//     Ctor x y
//   in
//   rcd

// %splice[] (autolift_binds [`%eg_ctor])

// [@@Tac.preprocess_with preprocess]
// let eg_pairsrec (add: stream int): stream (int & int) =
//   // recursive streams sometimes need annotations
//   let rec xy: stream (int & int) =
//     let x = 0 `fby` fst xy + add in
//     let y = 0 `fby` snd xy - add in
//     (x, y)
//   in
//   xy

// %splice[] (autolift_binds [`%eg_pairsrec])

// type record = { x: int; y: int; }

// instance has_stream_record: Shallow.has_stream record = {
//   ty_id       = [`%record];
//   val_default = { x = 0; y = 0; };
// }


// // XXX:TODO: preprocess breaks on records?
// [@@Tac.preprocess_with preprocess; source]
// let eg_record (add: stream int): stream int =
//   let x = 0 `fby` add in
//   let y = 1 `fby` add in
//   let xy = { x; y } in
//   xy.x


// %splice[] (autolift_binds [`%eg_record])

// let eg_streaming_if (x: stream int): stream int =
//   if x >= 0 then x else -x

// %splice[] (autolift_binds [`%eg_streaming_if])

// let eg_streaming_match_lets (x: stream int): stream int =
//   let cond = x >= 0 in
//   let abs =
//     match cond with
//       | true -> x
//       | false -> -x
//   in abs

// %splice[] (autolift_binds [`%eg_streaming_match_lets])

// let eg_static_match (consts: list int) (x: stream int): stream int =
//   match consts with
//   | [] -> 0
//   | (c: int) :: _ -> c + x

// %splice[] (autolift_binds [`%eg_static_match])

// let silly_id (x: int): y: int { x == y } = x

// (*** Examples / test cases ***)
// [@@source]
// let eg_refinement0 (x: stream int): stream int =
//   silly_id x

// %splice[] (autolift_binds [`%eg_refinement0])

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

// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y

// %splice[] (autolift_binds [`%eg_instantiate_lemma])
