(* Fixed-size 64-bit bit-vectors.
  This uses FStar.UInt64 as an implementation so it can generate fixed-width C
  code, and uses FStar.BV as the specification so the SMT solver can reason
  about it.
*)
module Network.TTCan.Base.BV64

module U8   = FStar.UInt8
module BITS = FStar.UInt64
module Cast = FStar.Int.Cast

module UInt = FStar.UInt

module BV   = FStar.BV

module Tac = FStar.Tactics

let n = BITS.n

type index_t = i: U8.t { U8.v i < n }

let t = BITS.t

type abs = BV.bv_t n

let v (bv: BITS.t) = BV.int2bv #n (BITS.v bv)
let v_64 (bv: BITS.t): BV.bv_t 64 = v bv

let zero: z: t { v z = BV.int2bv #n 0 } = 0uL

let one: z: t { v z = BV.int2bv #n 1 } = 1uL

(* XXX:REORG: lemmas taken from Vale.Math.Bits (Apache licence) in hacl-star
  https://github.com/hacl-star/hacl-star/blob/main/vale/code/lib/math/Vale.Math.Bits.fst *)
let lemma_logand (#n: pos) (a: UInt.uint_t n) (b:UInt.uint_t n): Lemma
  (BV.int2bv #n (UInt.logand #n a b) == BV.bvand #n (BV.int2bv a) (BV.int2bv b)) =
  BV.int2bv_logand #n #a #b #(BV.bvand #n (BV.int2bv #n a) (BV.int2bv #n b)) ();
  assert_norm (BV.int2bv #n (UInt.logand #n a b) == BV.bvand #n (BV.int2bv a) (BV.int2bv b))

let lemma_logxor (#n: pos) (a: UInt.uint_t n) (b:UInt.uint_t n): Lemma
  (BV.int2bv #n (UInt.logxor #n a b) == BV.bvxor #n (BV.int2bv a) (BV.int2bv b)) =
  BV.int2bv_logxor #n #a #b #(BV.bvxor #n (BV.int2bv #n a) (BV.int2bv #n b)) ();
  assert_norm (BV.int2bv #n (UInt.logxor #n a b) == BV.bvxor #n (BV.int2bv a) (BV.int2bv b))

let lemma_logor (#n: pos) (a: UInt.uint_t n) (b:UInt.uint_t n): Lemma
  (BV.int2bv #n (UInt.logor #n a b) == BV.bvor #n (BV.int2bv a) (BV.int2bv b)) =
  BV.int2bv_logor #n #a #b #(BV.bvor #n (BV.int2bv #n a) (BV.int2bv #n b)) ();
  assert_norm (BV.int2bv #n (UInt.logor #n a b) == BV.bvor #n (BV.int2bv a) (BV.int2bv b))

let lemma_lognot (#n: pos) (a: UInt.uint_t n): Lemma
  (BV.int2bv #n (UInt.lognot #n a) == BV.bvnot #n (BV.int2bv a)) =
  BV.int2bv_lognot #n #a #(BV.bvnot #n (BV.int2bv #n a)) ();
  assert_norm (BV.int2bv #n (UInt.lognot #n a) == BV.bvnot #n (BV.int2bv a))

let lemma_shift_left (#n: pos) (a: UInt.uint_t n) (b:UInt.uint_t n) : Lemma
  (BV.int2bv #n (UInt.shift_left #n a b) == BV.bvshl #n (BV.int2bv a) b) =
  BV.int2bv_shl #n #a #b #(BV.bvshl #n (BV.int2bv #n a) b) ();
  assert_norm (BV.int2bv #n (UInt.shift_left #n a b) == BV.bvshl #n (BV.int2bv a) b)

let lemma_shift_right (#n: pos) (a: UInt.uint_t n) (b:UInt.uint_t n) : Lemma
  (BV.int2bv #n (UInt.shift_right #n a b) == BV.bvshr #n (BV.int2bv a) b) =
  BV.int2bv_shr #n #a #b #(BV.bvshr #n (BV.int2bv #n a) b) ();
  assert_norm (BV.int2bv #n (UInt.shift_right #n a b) == BV.bvshr #n (BV.int2bv a) b)

(* LATER: lemmas for inequality, addition, subtraction, multiplication, division, modulus *)


let logand (a b: BITS.t): Pure BITS.t
    (requires True)
    (ensures (fun c -> v c == BV.bvand #n (v a) (v b))) =
  let c = a `BITS.logand` b in
  lemma_logand #n (BITS.v a) (BITS.v b);
  c

let logor (a b: BITS.t): c: BITS.t { v c == BV.bvor #n (v a) (v b) } =
  let c = a `BITS.logor` b in
  lemma_logor #n (BITS.v a) (BITS.v b);
  c

let lognot (a: BITS.t): c: BITS.t { v c == BV.bvnot #n (v a) } =
  let c = BITS.lognot a in
  lemma_lognot #n (BITS.v a);
  c

let shift_left (a: BITS.t) (b: index_t): c: BITS.t { v c == BV.bvshl #n (v a) (U8.v b) } =
  let c = a `BITS.shift_left` (Cast.uint8_to_uint32 b) in
  lemma_shift_left #n (BITS.v a) (U8.v b);
  c

let shift_right (a: BITS.t) (b: index_t): c: BITS.t { v c == BV.bvshr #n (v a) (U8.v b) } =
  let c = a `BITS.shift_right` (Cast.uint8_to_uint32 b) in
  lemma_shift_right #n (BITS.v a) (U8.v b);
  c

let lemma_v_inj (a b: BITS.t):
  Lemma (v a == v b <==> a == b) =
  if a = b
  then assert (v a == v b)
  else (
    if v a = v b
    then (
      // contradiction: v a = v b but a <> b
      BV.int2bv_lemma_2 #n (BITS.v a) (BITS.v b);
      false_elim ())
    else (
      assert (v a <> v b)
    )
  )

let eq (a b: BITS.t): Pure bool
    (requires True)
    (ensures (fun c -> c <==> v a == v b)) =
  lemma_v_inj a b;
  a = b

let ne (a b: BITS.t): Pure bool
    (requires True)
    (ensures (fun c -> v a <> v b <==> c)) =
  lemma_v_inj a b;
  a <> b
