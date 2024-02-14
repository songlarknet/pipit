(* Fixed-size message-status-count vector.
  This module uses 64-bit storage. Each counter is three bits, so we stripe
  each counter into three bit-vectors.
  The module is currently unverified.
  *)
module Network.TTCan.Prim.MSC64

module SugarBase = Pipit.Sugar.Base
module Sugar     = Pipit.Sugar.Shallow
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module BV64  = PipitRuntime.Bits.BV64
module BV64X3 = PipitRuntime.Bits.BV64.X3
module S32R  = Network.TTCan.Prim.S32R
module Types = Network.TTCan.Types

module U8    = FStar.UInt8
module U64   = FStar.UInt64
module BV    = FStar.BV
module Tac   = FStar.Tactics

type index_t = Types.trigger_index

type t = BV64X3.t

instance has_stream_t: Sugar.has_stream t = {
  ty_id = [`%t];
  val_default = BV64X3.zero;
}

(* Look up MSC at given index *)
let index (bvs: t) (i: index_t): Types.message_status_counter =
  S32R.u8_to_s32r (BV64X3.index_read bvs (S32R.s32r_to_u8 i))

(* Set MSC at given index to zero *)
let clear (bvs: t) (i: index_t): t =
  BV64X3.clear bvs (S32R.s32r_to_u8 i)

(* Set MSC at given index to given value *)
let update (bvs: t) (i: index_t) (v: Types.message_status_counter): t =
  BV64X3.update bvs (S32R.s32r_to_u8 i) (S32R.s32r_to_u8 v)

(* Array of all-zero counters *)
let zero: t = BV64X3.zero
