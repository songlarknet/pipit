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
module S32R  = Network.TTCan.Prim.S32R
module Types = Network.TTCan.Types

module U8    = FStar.UInt8
module U64   = FStar.UInt64
module BV    = FStar.BV
module Tac   = FStar.Tactics

// Each message status count is 3-bits, so we can fit 21 of them in 64 bits.
// We want to be able to reset the whole array to zero within a single clock, so
// limiting it to a few words is ideal.
let index_count = 21
type index_t = Types.app_message_index

type t = BV64.t

(* Internal: convert index to 64-bit index *)
let shift_index' (i: index_t): BV64.index_t =
  U8.(S32R.s32r_to_u8' i *^ 3uy)

(* Internal: mask of where a particular index's values are *)
let index_mask' (i: index_t): BV64.t =
  (7uL <: BV64.t) `BV64.shift_left` shift_index' i

(* Internal: mask away irrelevant bits to get 3-bit counter *)
let extract_u64_to_msc' (i: BV64.t): r: U64.t { U64.v r <= 7 } =
  let masked = i `BV64.logand` 7uL in
  assert (BV.bv2int #64 (BV64.v masked) <= 7)
    by (Tac.compute (); BV64.tac_simp ());
  BV64.lemma_bv2int_v masked;
  masked

private
let mk_msc' (i: U64.t { U64.v i <= 7 }): Types.message_status_counter =
  S32R.u64_to_s32r' i

(* Look up MSC at given index *)
let index' (bv: BV64.t) (i: index_t): Types.message_status_counter =
  let shifted = (bv `BV64.logand` index_mask' i) `BV64.shift_right` shift_index' i in
  mk_msc' (extract_u64_to_msc' shifted)

(* Set MSC at given index to zero *)
let clear' (bv: BV64.t) (i: index_t): BV64.t =
  bv `BV64.logand` BV64.lognot (index_mask' i)

(* Set MSC at given index to given value *)
let update' (bv: BV64.t) (i: index_t) (v: Types.message_status_counter): BV64.t =
  let bv = clear' bv i in
  bv `BV64.logor` (S32R.s32r_to_u64' v `BV64.shift_left` shift_index' i)

let zero: BV64.t = BV64.zero

%splice[index]  (SugarTac.lift_prim "index"  (`index'))
%splice[clear]  (SugarTac.lift_prim "clear"  (`clear'))
%splice[update] (SugarTac.lift_prim "update" (`update'))
