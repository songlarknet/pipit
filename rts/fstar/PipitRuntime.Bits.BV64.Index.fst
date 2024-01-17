(* Operations for indexing into 64-bit bit-vectors.
  This module contains helpers for treating 64-bit uints as arrays of booleans.
  The module can be extracted to C.
  It is currently unverified.
*)
module PipitRuntime.Bits.BV64.Index
module U8   = FStar.UInt8
module BV64 = PipitRuntime.Bits.BV64
module Tac  = FStar.Tactics

module BV = FStar.BV

let index_mask (i: BV64.index_t): BV64.t =
  BV64.one `BV64.shift_left` i

let index_read (bv: BV64.t) (i: BV64.index_t): bool =
  (bv `BV64.logand` index_mask i) `BV64.ne` BV64.zero

let set (bv: BV64.t) (i: BV64.index_t): BV64.t =
  bv `BV64.logor` index_mask i

let clear (bv: BV64.t) (i: BV64.index_t): BV64.t =
  bv `BV64.logand` BV64.lognot (index_mask i)

let update (bv: BV64.t) (i: BV64.index_t) (v: bool): BV64.t =
  if v then set bv i else clear bv i

// Shelved: spec: pending upstream raw bitvector operations.

// let update_spec' (bv bv': BV64.t) (i: BV64.index_t) (v: bool) (j: BV64.index_t): prop =
//   index bv' j = (if i = j then v else index bv j)

// let update_spec (bv bv': BV64.t) (i: BV64.index_t) (v: bool): prop =
//   forall (j: BV64.index_t).
//     update_spec' bv bv' i v j

// let lemma_set_spec' (bv: BV64.t) (i: BV64.index_t) (j: BV64.index_t)
//     : Lemma (update_spec' bv (set bv i) i true j) =
//   // if i = j
//   // then assert (update_spec' bv (set bv i) i true j)
//   //   by 
//   //     (Tac.norm [delta; zeta; iota; primops]; BV64.tac_simp (); Tac.dump "X")
//   // else
