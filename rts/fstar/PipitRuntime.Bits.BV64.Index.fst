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

let index (bv: BV64.t) (i: BV64.index_t): bool =
  (bv `BV64.logand` index_mask i) `BV64.ne` BV64.zero

let set (bv: BV64.t) (i: BV64.index_t): BV64.t =
  bv `BV64.logor` index_mask i

let clear (bv: BV64.t) (i: BV64.index_t): BV64.t =
  bv `BV64.logand` BV64.lognot (index_mask i)

let update (bv: BV64.t) (i: BV64.index_t) (v: bool): BV64.t =
  if v then set bv i else clear bv i

// Shelved: spec: pending...

// let update_spec' (bv bv': BV64.t) (i: BV64.index_t) (v: bool) (j: BV64.index_t): prop =
//   index bv' j = (if i = j then v else index bv j)

// let update_spec (bv bv': BV64.t) (i: BV64.index_t) (v: bool): prop =
//   forall (j: BV64.index_t).
//     update_spec' bv bv' i v j

// let lemma_test (bv: FStar.UInt.uint_t 64) (i j: nat):
//   Lemma true =
//   assert ((BV.bvand #64 (BV.bvor #64 (BV.int2bv #64 bv) (BV.bvshl #64 (BV.int2bv #64 1) i)) (BV.bvshl #64 (BV.int2bv #64 1) i) <> BV.int2bv #64 0 == true))
//   // assert (i <> j ==>
//   // (BV.bvand (BV.bvor (BV.int2bv bv) (BV.bvshl (BV.int2bv 1) i))
//   //     (BV.bvshl (BV.int2bv 1) j) <>
//   //   BV.int2bv 0 =
//   //   (match i = j with
//   //     | true -> true
//   //     | _ -> BV.bvand (BV.int2bv bv) (BV.bvshl (BV.int2bv 1) j) <> BV.int2bv 0) ==
//   //   true)
//   // )

// let lemma_set_spec' (bv: BV64.t) (i: BV64.index_t) (j: BV64.index_t)
//     : Lemma (update_spec' bv (set bv i) i true j) =
//   // if i = j
//   // then assert (update_spec' bv (set bv i) i true j)
//   //   by 
//   //     (Tac.norm [delta; zeta; iota; primops]; BV64.tac_simp (); Tac.dump "X")
//   // else
//   assert (update_spec' bv (set bv i) i true j) by
//     (
//      Tac.norm [delta; zeta; iota; primops];
//      Tac.dump "PRE";
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      Tac.dump "POST";
//      Tac.norm [delta_namespace ["Network"]; zeta; nbe; iota; primops];
//      Tac.dump "PRE";
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      BV64.tac_simp ();
//      Tac.dump "POST";
//      BV64.tac_simp_in_env ();
//      Tac.dump "POST2"
//      );
//   ()

// let lemma_set_spec (bv: BV64.t) (i: BV64.index_t)
//     : Lemma (update_spec bv (set bv i) i true) =

// let lemma_test_bvand (a b: BV64.t): Lemma (BV64.v (a `BV64.logand` b) == BV.bvand #64 (BV64.v a) (BV64.v b)) =
//   ()

// let lemma_test_bvshl (a: BV64.t) (i: BV64.index_t): Lemma (BV64.v (a `BV64.shift_left` i) = BV.bvshl #64 (BV64.v a) (U8.v i)) =
//   assert (BV64.v (a `BV64.shift_left` i) = BV.bvshl #64 (BV64.v a) (U8.v i))
//     ; // by (Tac.norm [delta_only [`%BV64.n]]; Tac.dump "X");
//   ()

// #set-options "--print_implicits"

// This lemma is a pain: it requires the bit-vector to be the exact constant 64 (not BV64.n).
// But, we can't rewrite in the environment because of a bug in F*, so just disable it for now...
// let lemma_test_bvshl_bvand (x a: BV64.t) (i: BV64.index_t): Lemma true = // (BV64.v (x `BV64.logand` (a `BV64.shift_left` i)) = BV.bvand #BV64.n (BV64.v x) (BV.bvshl #BV64.n (BV64.v a) (U8.v i))) =
//   assert (BV64.v (x `BV64.logand` (a `BV64.shift_left` i)) == BV.bvand #64 (BV64.v x) (BV.bvshl #64 (BV64.v a) (U8.v i)))
//     by (Tac.compute (); BV64.tac_simp (); Tac.dump "X");
//   ()





// let mask_raw (i: nat { i < 8 }) : BV.bv_t 8 =
//   BV.int2bv 1 `BV.bvshl` i

// let index_raw (bv: BV.bv_t 8) (i: nat { i < 8 }) : bool =
//   (bv `BV.bvand` mask_raw i) <> BV.int2bv 0

// let lemma_index_zero_raw (i: nat { i < 8 }): Lemma (not (index_raw (BV.int2bv 0) i)) =
//   // assert_norm (not (index_raw (BV.int2bv 0) i));
//   // assert (not (index_raw (BV.int2bv 0) i)) by (Tac.norm [delta]; Tac.dump "X");
//   ()

// let lemma_index_zero (i: BV64.index_t): Lemma (not (index BV64.zero i)) =
//   // lemma_index_zero_raw (U8.v i);
//   // assert (1 == U8.v BV64.one);
//   // assert (BV.int2bv 1 == BV.int2bv (U8.v BV64.one));
//   // assert_norm (BV.int2bv 1 == BV64.v BV64.one);
//   // assume (BV.int2bv 1 == BV64.v BV64.one);
//   // assert (BV.int2bv 1 == BV64.v BV64.one) by (Tac.norm [delta]; Tac.dump "X");
//   // assert (BV64.v (BV64.shift_left BV64.one i) == BV.bvshl (BV64.v BV64.one) (U8.v i));
//   // assert ((BV64.v (BV64.shift_left BV64.one i) == (BV.bvshl (BV.int2bv 1) (U8.v i))));
//   // assert ((BV64.v (BV64.shift_left BV64.one i) == (BV.bvshl #8 (BV.int2bv 1) (U8.v i))));
//   // assert ((BV64.v (BV64.shift_left BV64.one i) == (BV.bvshl #8 (BV.int2bv 1) (U8.v i) <: BV.bv_t 8)));

//   // assert (BV64.v (mask i) == mask_raw (U8.v i)) by (Tac.norm [delta_only [`%mask; `%mask_raw]]; Tac.dump "X");
//   // assert (BV64.v (mask i) == mask_raw (U8.v i)); // by (Tac.norm [delta]; Tac.dump "X");
//   // assert_norm ((BV.int2bv 0 `BV.bvand` mask_raw (U8.v i)) = BV.int2bv 0);
//   // assert (BV64.v (BV64.zero `BV64.logand` mask i) = (BV64.v BV64.zero `BV.bvand` mask_raw (U8.v i)));
//   // assert (not (index 0uL i)) by (Tac.norm [delta]; Tac.dump "X");
//   ()


// // let zero: z: t { forall (i: index_t). not (index z i) } =
// //   0uL
// //   // assert (index bv 0uy = false);
// //   // assert_norm (UInt.logand #64 0 1 == 0);
// //   // assert (UInt.logand #64 0 1 == 0) by (FStar.Tactics.BV.bv_tac ());
// //   // assert (UInt.logand #64 0 1 == 0) by (FStar.Tactics.BV.bv_tac ());
  
