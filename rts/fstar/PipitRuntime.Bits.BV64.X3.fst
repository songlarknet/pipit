(* Fixed-size message-status-count vector.
  This module uses 64-bit storage. Each counter is three bits, so we fit 21
  counters into a U64.
  The module is currently unverified.
  *)
module PipitRuntime.Bits.BV64.X3

module BV64  = PipitRuntime.Bits.BV64
module BV64I = PipitRuntime.Bits.BV64.Index

module U8    = FStar.UInt8
module U64   = FStar.UInt64
module Cast  = FStar.Int.Cast
module BV    = FStar.BV
module Tac   = FStar.Tactics

type index_t = BV64.index_t

type t = { bv0: BV64.t; bv1: BV64.t; bv2: BV64.t; }

type x3 = x3: U8.t { U8.v x3 <= 7 }

#push-options "--fuel 1 --ifuel 0"

private
let mk_x3 (b0 b1 b2: bool): x3 =
  let open U8 in
  (if b0 then 1uy else 0uy) +^
  (if b1 then 2uy else 0uy) +^
  (if b2 then 4uy else 0uy)

(* Look up MSC at given index *)
let index_read (bvs: t) (i: index_t): x3 =
  mk_x3 (BV64I.index_read bvs.bv0 i) (BV64I.index_read bvs.bv1 i) (BV64I.index_read bvs.bv2 i)

(* Set MSC at given index to zero *)
let clear (bvs: t) (i: index_t): t =
  { bv0 = BV64I.clear bvs.bv0 i; bv1 = BV64I.clear bvs.bv1 i; bv2 = BV64I.clear bvs.bv2 i; }

(* Set MSC at given index to given value *)
let update (bvs: t) (i: index_t) (v: x3): t =
  let v' = Cast.uint8_to_uint64 v in
  { bv0 = BV64I.update bvs.bv0 i (v' `BV64.logand` 1uL <> 0uL); bv1 = BV64I.update bvs.bv1 i  (v' `BV64.logand` 2uL <> 0uL); bv2 = BV64I.update bvs.bv2 i  (v' `BV64.logand` 4uL <> 0uL); }

let zero: t = { bv0 = 0uL; bv1 = 0uL; bv2 = 0uL; }
