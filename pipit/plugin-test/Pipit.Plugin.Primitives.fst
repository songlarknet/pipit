module Pipit.Plugin.Primitives

open Pipit.Plugin.Interface
open Pipit.Plugin.Primitives

module PXB = Pipit.Exp.Base
module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table


// define fby primitive by manually lifting
let fby (#a: eqtype) {| PSSB.has_stream a |} (dflt: a) (strm: a): a = dflt

[@@core_lifted; core_of_source "Plugin.Test.CoreLift.fby" (ModeFun Static false (ModeFun Static false (ModeFun Static true (ModeFun Stream true Stream))))]
let fby_core (ctx: PPT.context PPS.table) (#a: eqtype) {| PSSB.has_stream a |}
  (dflt: a) (strm: PXB.exp PPS.table ctx (PSSB.shallow a)): PXB.exp PPS.table ctx (PSSB.shallow a) =
  PXB.XFby dflt strm

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