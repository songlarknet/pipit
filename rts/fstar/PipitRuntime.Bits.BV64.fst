(* Fixed-size 64-bit bit vectors.
  This uses FStar.UInt64 as an implementation so it can generate fixed-width C
  code, and uses FStar.BV as the specification so the SMT solver can reason
  about it.

  Bit vectors are kind of fiddly. There are a few caveats:
  * The type `FStar.BV.bv_t 64` is translated using SMT bit vector theory. This
    type is very good for reasoning about the actual bits.
  * The type `FStar.BV.bv_t n` is translated as an abstract bit vector, which
    may be implemented as a list. This abstract type seems to be better for
    algebraic operations on the whole vector.
  * The abstract bitvector is used even if `n` has a concrete value in the
    environment: `let n = 64; ... bv_t n` is treated as an abstract bit vector.
  * The bit vector operations take the length as an implicit argument, but it's
    often necessary to specify the length manually. Although the inferred
    length may be logically equivalent to the right length, it actually needs
    the *syntactically* correct length. For this reason, it's also useful to
    enable `--print_implicits`.
  * Although both `bv_t 64` and `bv_t n` have distinct advantages, going
    between the two is fiddly. To do this, there is a tactic `tac_hide_n`
    to replace all occurrences of 64 with n. The tactic does a normalize
    step first to try to expose any occurences of `n` hiding in functions,
    though perhaps we really want to replace the occurrences inside function
    definitions somehow.
  * Sometimes, it is sufficient to normalize the goal, eg with assert_norm.
*)
module PipitRuntime.Bits.BV64

module U8   = FStar.UInt8
module BITS = FStar.UInt64
module Cast = FStar.Int.Cast

module UInt = FStar.UInt

module BV   = FStar.BV

module Tac = FStar.Tactics

#set-options "--print_implicits"

let n = BITS.n

type index_t = i: U8.t { U8.v i < n }

let t = BITS.t

type abs = BV.bv_t 64

[@@"tac_opaque"]
let v (bv: BITS.t) = BV.int2bv #64 (BITS.v bv)

let zero: i: t { v i == BV.int2bv #64 0 } =
  let i = 0uL in
  assert (v i == BV.int2bv #64 0)
    by (Tac.norm [delta_only [`%v]]);
  i

let one: i: t { v i = BV.int2bv #64 1 } =
  let i = 1uL in
  assert (v i == BV.int2bv #64 1)
    by (Tac.norm [delta_only [`%v]]);
  i

(**** Lemmas ****)
(* Abstraction: hiding n so the SMT bit-vector theory doesn't kick in *)
let lemma_hide_n (): Lemma (64 == n) = ()
let tac_hide_n (): Tac.Tac unit =
  Tac.compute ();
  Pipit.Tactics.top_down_in_env [`lemma_hide_n]

let lemma_v_inj (a b: BITS.t):
  Lemma (v a == v b <==> a == b) =
  if a = b
  then assert (v a == v b)
  else (
    if v a = v b
    then (
      // contradiction: v a = v b but a <> b
      BV.int2bv_lemma_2 #64 (BITS.v a) (BITS.v b);
      false_elim ())
    else (
      assert (v a <> v b)
    )
  )

let lemma_bv2int_v (a: BITS.t):
  Lemma (BV.bv2int (v a) == BITS.v a) =
  BV.inverse_num_lemma #64 (BITS.v a);
  assert (BV.bv2int (v a) == BITS.v a)
    by (Tac.norm [delta_only [`%v]])

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


[@@"tac_opaque"]
let logand (a b: BITS.t): Pure BITS.t
    (requires True)
    (ensures (fun c -> v c == BV.bvand #64 (v a) (v b))) =
  let c = a `BITS.logand` b in
  lemma_logand #64 (BITS.v a) (BITS.v b);
  assert (v c == BV.bvand #64 (v a) (v b))
    by (Tac.norm [delta_only [`%v]]);
  c

[@@"tac_opaque"]
let logor (a b: BITS.t): c: BITS.t { v c == BV.bvor #64 (v a) (v b) } =
  let c = a `BITS.logor` b in
  lemma_logor #64 (BITS.v a) (BITS.v b);
  assert (v c == BV.bvor #64 (v a) (v b))
    by (Tac.norm [delta_only [`%v]]);
  c

[@@"tac_opaque"]
let lognot (a: BITS.t): c: BITS.t { v c == BV.bvnot #64 (v a) } =
  let c = BITS.lognot a in
  lemma_lognot #64 (BITS.v a);
  // Normalizing the goal here is not sufficient, though I'm not sure why
  assert (v c == BV.bvnot #64 (v a))
    by (Tac.norm [delta_only [`%v]]; tac_hide_n ());
  c

[@@"tac_opaque"]
let shift_left (a: BITS.t) (b: index_t): c: BITS.t { v c == BV.bvshl #64 (v a) (U8.v b) } =
  let c = a `BITS.shift_left` (Cast.uint8_to_uint32 b) in
  lemma_shift_left #64 (BITS.v a) (U8.v b);
  assert (v c == BV.bvshl #64 (v a) (U8.v b))
    by (Tac.norm [delta_only [`%v]]);
  c

[@@"tac_opaque"]
let shift_right (a: BITS.t) (b: index_t): c: BITS.t { v c == BV.bvshr #64 (v a) (U8.v b) } =
  let c = a `BITS.shift_right` (Cast.uint8_to_uint32 b) in
  lemma_shift_right #64 (BITS.v a) (U8.v b);
  assert (v c == BV.bvshr #64 (v a) (U8.v b))
    by (Tac.norm [delta_only [`%v]]);
  c

[@@"tac_opaque"]
let eq (a b: BITS.t): Pure bool
    (requires True)
    (ensures (fun c -> c <==> v a == v b)) =
  lemma_v_inj a b;
  a = b

[@@"tac_opaque"]
let ne (a b: BITS.t): Pure bool
    (requires True)
    (ensures (fun c -> v a <> v b <==> c)) =
  lemma_v_inj a b;
  a <> b


let lemma_simp_logand (a b: BITS.t): Lemma
  (v (logand a b) == BV.bvand #64 (v a) (v b)) = ()

let lemma_simp_logor (a b: BITS.t): Lemma
  (v (logor a b) == BV.bvor #64 (v a) (v b)) = ()

let lemma_simp_lognot (a: BITS.t): Lemma
  (v (lognot a) == BV.bvnot #64 (v a)) = ()

let lemma_simp_shift_left (a: BITS.t) (b: index_t): Lemma
  (v (shift_left a b) == BV.bvshl #64 (v a) (U8.v b)) = ()

let lemma_simp_shift_right (a: BITS.t) (b: index_t): Lemma
  (v (shift_right a b) == BV.bvshr #64 (v a) (U8.v b)) = ()

let lemma_simp_eq (a b: BITS.t): Lemma
  (eq a b == (v a = v b)) = ()

let lemma_simp_ne (a b: BITS.t): Lemma
  (ne a b == (v a <> v b)) = ()

let tac_simp_lems: list Tac.term =
  [`lemma_simp_logand;
    `lemma_simp_logor;
    `lemma_simp_lognot;
    `lemma_simp_shift_left;
    `lemma_simp_shift_right;
    `lemma_simp_eq;
    `lemma_simp_ne;]

(* Would it be easier to extend bv_tac to work on 64-bit? *)
let tac_simp (): Tac.Tac unit =
  Pipit.Tactics.top_down tac_simp_lems

let tac_simp_in_env (): Tac.Tac unit =
  Pipit.Tactics.top_down_in_env tac_simp_lems
