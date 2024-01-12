(* Fixed-size message-status-count vector.
  This module uses 64-bit storage. Each counter is three bits, so we fit 21
  counters into a U64.
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

// Each message status count is 3-bits, so we can fit 21 of them in 64 bits.
// We want to be able to reset the whole array to zero within a single clock, so
// limiting it to a few words is ideal.
let index_count = 64
type index_t = Types.app_message_index

type t = BV64X3.t

instance has_stream_t: Sugar.has_stream t = {
  ty_id = [`%t];
  val_default = BV64X3.zero;
}

(* Look up MSC at given index *)
let index' (bvs: t) (i: index_t): Types.message_status_counter =
  S32R.u8_to_s32r' (BV64X3.index_read bvs (S32R.s32r_to_u8' i))

(* Set MSC at given index to zero *)
let clear' (bvs: t) (i: index_t): t =
  BV64X3.clear bvs (S32R.s32r_to_u8' i)

(* Set MSC at given index to given value *)
let update' (bvs: t) (i: index_t) (v: Types.message_status_counter): t =
  BV64X3.update bvs (S32R.s32r_to_u8' i) (S32R.s32r_to_u8' v)

let zero: t = BV64X3.zero

%splice[index]  (SugarTac.lift_prim "index"  (`index'))
%splice[clear]  (SugarTac.lift_prim "clear"  (`clear'))
%splice[update] (SugarTac.lift_prim "update" (`update'))
