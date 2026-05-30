module Plugin.Test.HasStream.Pair

(* Hand-written sanity checks that F* can derive `has_stream (a & b)` from
   local `has_stream a` and `has_stream b` via the `has_stream_tup2` instance
   in `Pipit.Prim.HasStream`. Mirrors the shape of the spliced `fst_core`
   signature produced by the polymorphic `fst`/`snd` in `Plugin.Test`. *)

module PSSB = Pipit.Prim.HasStream
module PXB  = Pipit.Exp.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table

(* 1. Pure signature: does the typeclass `has_stream (a & b)` resolve? *)
let _test_tc (#a #b: eqtype) {| PSSB.has_stream a |} {| PSSB.has_stream b |}
  : PXB.exp PPS.table [PSSB.shallow (a & b)] (PSSB.shallow a) = admit ()

(* 2. Real body using `PSSB.shallow (a & b)` as the argument shape. *)
let _test_tc2 (#a #b: eqtype) {| PSSB.has_stream a |} {| PSSB.has_stream b |}
  : PXB.exp PPS.table [PSSB.shallow (a & b)] (PSSB.shallow a) =
  PXB.XApps
    (PXB.XApp
        (PXB.XPrim
          (PPS.mkPrim (Some "FStar.Pervasives.Native.fst")
              (PPT.FTFun (PSSB.shallow (a & b))
                  (PPT.FTVal (PSSB.shallow a)))
              FStar.Pervasives.Native.fst))
        (PXB.XBase (PXB.XBVar 0)))
