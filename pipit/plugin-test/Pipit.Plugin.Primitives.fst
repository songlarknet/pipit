module Pipit.Plugin.Primitives

open Pipit.Plugin.Interface
open Pipit.Plugin.Primitives

module PXB = Pipit.Exp.Base
module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table
module PPL = Pipit.Plugin.Lift


// define fby primitive by manually lifting
let fby (#a: eqtype) {| PSSB.has_stream a |} (dflt: a) (strm: a): a = dflt

[@@core_lifted; core_of_source "Plugin.Test.CoreLift.fby" (ModeFun Static false (ModeFun Static false (ModeFun Static true (ModeFun Stream true Stream))))]
let fby_core (ctx: PPT.context PPS.table) (#a: eqtype) {| PSSB.has_stream a |}
  (dflt: a) (strm: PXB.exp PPS.table ctx (PSSB.shallow a)): PXB.exp PPS.table ctx (PSSB.shallow a) =
  PXB.XFby dflt strm

// specialise if-then-else? maybe we should generate better expressions for if-then-else.
// for streaming conditionals, it might be better to generate simple folds functions and reuse them...
// [@@source_mode (ModeFun Static false (ModeFun Static false (ModeFun Stream true (ModeFun Stream true (ModeFun Stream true Stream)))))]
// let if_then_else (#a: eqtype) {| PSSB.has_stream a |} (p: bool) (t f: a): a =
//   if p then t else f

// %splice[] (PPL.lift_tac1 "if_then_else")

// let rec' (#a: eqtype) {| PSSB.has_stream a |} (f: a -> a): a = admit ()

// rec can't currently be implemented here, because the contexts required for rec are a bit weird. instead, it's special-cased in lift_tac
// [@@core_lifted; core_of_source "Plugin.Test.CoreLift.rec'" (ModeFun Static false (ModeFun Static false (ModeFun (ModeFun Stream true Stream) true Stream)))]
// let rec_core (ctx: PPT.context PPS.table) (#a: eqtype) {| PSSB.has_stream a |}
//   (f: PXB.exp PPS.table (PSSB.shallow a :: ctx) (PSSB.shallow a) -> PXB.exp PPS.table (PSSB.shallow a :: ctx) (PSSB.shallow a)): PXB.exp PPS.table ctx (PSSB.shallow a) =
//   PXB.XMu (
//     let x = PXB.XBase (PXB.XBVar 0) in
//     f x)

// TODO check : bool -> unit
// contract?