(* Fixed-size 64-bit bit-vectors.
  This uses FStar.UInt64 as an implementation so it can generate fixed-width C
  code, and uses FStar.BV as the specification so the SMT solver can reason
  about it.
*)
module Network.TTCan.Base.BV64

module U8   = FStar.UInt8
module BITS = FStar.UInt64
module BV   = FStar.BV

// Reduce to tiny to debug some issues....
let n = 64 // BITS.n

type index_t = i: U8.t { U8.v i < 64 }

assume new
type t  // = BITS.t

type abs = BV.bv_t 64

val v (bv: t): abs
// let v (bv: BITS.t): abs = BV.int2bv (BITS.v bv)

val zero: z: t { v z = BV.int2bv 0 } // = 0uL

val one: z: t { v z = BV.int2bv 1 }  // = 1uL


val logand (a b: t): Pure t
    (requires True)
    // specifying explicit bit size = 64 here seems necessary for proofs in BV64X. leaving as n doesn't work
    (ensures (fun c -> v c == BV.bvand #64 (v a) (v b)))

val logor (a b: t): Pure t
    (requires True)
    (ensures (fun c -> v c == BV.bvor #64 (v a) (v b)))

val lognot (a: t): Pure t
    (requires True)
    (ensures (fun c -> v c == BV.bvnot #64 (v a)))

val shift_left (a: t) (b: index_t): Pure t
    (requires True)
    (ensures (fun c -> v c == BV.bvshl #64 (v a) (U8.v b)))

val shift_right (a: t) (b: index_t): Pure t
    (requires True)
    (ensures (fun c -> v c == BV.bvshr #64 (v a) (U8.v b)))

val eq (a b: t): Pure bool
    (requires True)
    (ensures (fun c -> c <==> v a = v b))

val ne (a b: t): Pure bool
    (requires True)
    (ensures (fun c -> c <==> v a <> v b))
