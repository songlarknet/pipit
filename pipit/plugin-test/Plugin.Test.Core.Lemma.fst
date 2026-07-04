(* Targeted reproduction at the core level of the SMT lemma-firing
   failure observed when `__ctx_*` helpers are emitted as plain
   top-level `let` (rather than `unfold let`).

   Background: the `Plugin.Test.Source.Lemma.eg_opaque_in_rec`
   `[@@proof_induct1]` discharge starts failing as soon as the lifter
   emits `__ctx_eg_opaque_in_rec_23` without the
   `Unfold_for_unification_and_vcgen` qualifier (Error 19 in the
   generated VC, line 103). The hypothesis under test: F* still
   passes a top-level let's definition to Z3 as an axiom, but Z3
   cannot chain it through `List.Tot.index` quickly enough to
   discharge the obligation.

   This module strips the failure all the way down to plain F* lemmas
   on plain top-level list lets, no plugin involved. *)
module Plugin.Test.Core.Lemma

module L  = FStar.List.Tot

#set-options "--z3rlimit 5"

(*** Probe 0: trivial top-level list literal, no `unfold`. ***)

let ctx0 : list int = [10; 20; 30]

(* If F* hands Z3 the definition of `ctx0` as an axiom, these should
   discharge instantly. *)
let _len_ctx0 () : Lemma (L.length ctx0 = 3) = ()
let _idx0_ctx0 () : Lemma (L.index ctx0 0 = 10) = ()
let _idx1_ctx0 () : Lemma (L.index ctx0 1 = 20) = ()
let _idx2_ctx0 () : Lemma (L.index ctx0 2 = 30) = ()


(*** Probe 1: same shape but split across a chain of top-level lets,
     mirroring the lifter's `__ctx_N = sty :: __ctx_(N-1)` pattern. ***)

let ctx_a0 : list int = []
let ctx_a1 : list int = 30 :: ctx_a0
let ctx_a2 : list int = 20 :: ctx_a1
let ctx_a3 : list int = 10 :: ctx_a2

let _len_a3  () : Lemma (L.length ctx_a3 = 3) = ()
let _idx0_a3 () : Lemma (L.index ctx_a3 0 = 10) = ()
let _idx1_a3 () : Lemma (L.index ctx_a3 1 = 20) = ()
let _idx2_a3 () : Lemma (L.index ctx_a3 2 = 30) = ()


(*** Probe 2: same as probe 1 but with `unfold` qualifiers,
     matching the shipped lifter behaviour. ***)

unfold let ctx_b0 : list int = []
unfold let ctx_b1 : list int = 30 :: ctx_b0
unfold let ctx_b2 : list int = 20 :: ctx_b1
unfold let ctx_b3 : list int = 10 :: ctx_b2

let _len_b3  () : Lemma (L.length ctx_b3 = 3) = ()
let _idx0_b3 () : Lemma (L.index ctx_b3 0 = 10) = ()
let _idx1_b3 () : Lemma (L.index ctx_b3 1 = 20) = ()
let _idx2_b3 () : Lemma (L.index ctx_b3 2 = 30) = ()


(*** Probe 3: longer chain (depth 9), plain top-level `let` — does Z3
     run out of fuel unfolding `index`/`length` through the chain?
     Both `length` and `index` are recursive functions; F* unfolds
     them via fuel-bounded axioms in the SMT encoding. ***)

let ctx_c0  : list int = []
let ctx_c1  : list int = 90 :: ctx_c0
let ctx_c2  : list int = 80 :: ctx_c1
let ctx_c3  : list int = 70 :: ctx_c2
let ctx_c4  : list int = 60 :: ctx_c3
let ctx_c5  : list int = 50 :: ctx_c4
let ctx_c6  : list int = 40 :: ctx_c5
let ctx_c7  : list int = 30 :: ctx_c6
let ctx_c8  : list int = 20 :: ctx_c7
let ctx_c9  : list int = 10 :: ctx_c8

(* Each of these would discharge instantly if `ctx_cN` were unfold. *)
#push-options "--z3rlimit 100 --fuel 30 --ifuel 30"
let _len_c9   () : Lemma (L.length ctx_c9 = 9) = ()
let _idx_c9_0 () : Lemma (L.index ctx_c9 0 = 10) = ()
let _idx_c9_8 () : Lemma (L.index ctx_c9 8 = 90) = ()
#pop-options


(*** Probe 4: same chain, but `unfold let`. ***)

unfold let ctx_d0  : list int = []
unfold let ctx_d1  : list int = 90 :: ctx_d0
unfold let ctx_d2  : list int = 80 :: ctx_d1
unfold let ctx_d3  : list int = 70 :: ctx_d2
unfold let ctx_d4  : list int = 60 :: ctx_d3
unfold let ctx_d5  : list int = 50 :: ctx_d4
unfold let ctx_d6  : list int = 40 :: ctx_d5
unfold let ctx_d7  : list int = 30 :: ctx_d6
unfold let ctx_d8  : list int = 20 :: ctx_d7
unfold let ctx_d9  : list int = 10 :: ctx_d8

#push-options "--z3rlimit 100 --fuel 30 --ifuel 30"
let _len_d9   () : Lemma (L.length ctx_d9 = 9) = ()
let _idx_d9_0 () : Lemma (L.index ctx_d9 0 = 10) = ()
let _idx_d9_8 () : Lemma (L.index ctx_d9 8 = 90) = ()
#pop-options
