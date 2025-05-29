(* Pipit streaming integration for 64-bit bit vectors *)
module Network.TTCan.Prim.BV64.Index

module SugarBase = Pipit.Sugar.Base
module Sugar     = Pipit.Sugar.Shallow
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module BV64      = PipitRuntime.Bits.BV64
module BV64I     = PipitRuntime.Bits.BV64.Index
module U64       = Network.TTCan.Prim.U64
module S32R      = Network.TTCan.Prim.S32R

type t = BV64.t
type index_t = S32R.t { min = 0; max = BV64.n - 1 }

let zero: U64.t = BV64.zero

let index (bv: t) (ix: index_t): bool =
  BV64I.index_read bv (S32R.s32r_to_u8 ix)

let set (bv: t) (ix: index_t): t =
  BV64I.set bv (S32R.s32r_to_u8 ix)

let clear (bv: t) (ix: index_t): t =
  BV64I.clear bv (S32R.s32r_to_u8 ix)

let update (bv: t) (ix: index_t) (v: bool): t =
  BV64I.update bv (S32R.s32r_to_u8 ix) v
