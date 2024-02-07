module Pipit.Sugar.Check

open Pipit.Prim.Table

open Pipit.Exp.Base

open Pipit.Sugar.Base
module Base = Pipit.Sugar.Base

module XC  = Pipit.Exp.Checked.Base
module XCC = Pipit.Exp.Checked.Compound
module PM  = Pipit.Prop.Metadata

// module SB  = Pipit.System.Base
module SI  = Pipit.System.Ind
module SX  = Pipit.System.Exp
module SXCE  = Pipit.System.Exp.Check.Entailment

type contract (t: table) (c: context t) (a: t.ty) (rely: XCC.cexp t c t.propty) (guar: XCC.cexp t (a :: c) t.propty) =
  impl: XCC.cexp t c a { XC.contract_valid rely guar impl }

let contract_of_exp1 (#t: table) (#a #b: t.ty) (r: XCC.cexp t [a] t.propty) (g: XCC.cexp t [b; a] t.propty) (i: XCC.cexp t [a] b  { XC.contract_valid r g i }): contract t [a] b r g = i

let contract_system_induct_k1' (#t: table) (#c: context t) (#a: t.ty) (r: XCC.cexp t c t.propty) (g: XCC.cexp t (a :: c) t.propty) (i: XCC.cexp t c a): prop =
  SI.induct1 (SX.system_of_contract r g i)

let exp_of_contract (#t: table) (#c: context t) (#a: t.ty) (#r: XCC.cexp t c t.propty) (#g: XCC.cexp t (a :: c) t.propty) (contr: contract t c a r g): XCC.cexp t c a =
  XCC.bless_contract r g contr

let stream_of_contract1 (#t: table) (#a #b: t.ty) (#r: XCC.cexp t [a] t.propty) (#g: XCC.cexp t [b; a] t.propty) (contr: contract t [a] b r g): stream t a -> stream t b =
  stream_of_exp1 (exp_of_contract contr)

// let stream_of_contract2 (#t: table) (#a #b #c: t.ty) (contr: contract t [a; b] c { XC.contract_valid contr.rely contr.guar contr.impl }): stream t a -> stream t b -> stream t c =
//   stream_of_exp2 (exp_of_contract contr)


let exp_of_stream0 (#t: table) (#ty: t.ty) (e: stream t ty) : XCC.cexp t [] ty = exp_of_stream0 e
let exp_of_stream1 (#t: table) (#a #b: t.ty) (f: stream t a -> stream t b) : XCC.cexp t [a] b = exp_of_stream1 f
let exp_of_stream2 (#t: table) (#a #b #c: t.ty) (f: stream t a -> stream t b -> stream t c) : XCC.cexp t [a; b] c = exp_of_stream2 f
let exp_of_stream3 (#t: table) (#a #b #c #d: t.ty) (f: stream t a -> stream t b -> stream t c -> stream t d) : XCC.cexp t [a; b; c] d = exp_of_stream3 f


let stream_of_checked0 (#t: table) (#a: t.ty) (e: XCC.cexp t [] a { XC.check_all PM.check_mode_unknown e }): stream t a =
  let e' = XCC.bless e in
  stream_of_exp0 e'

let stream_of_checked1 (#t: table) (#a #b: t.ty) (e: XCC.cexp t [a] b { XC.check_all PM.check_mode_unknown e }): stream t a -> stream t b =
  let e' = XCC.bless e in
  stream_of_exp1 e'

let stream_of_checked2 (#t: table) (#a #b #c: t.ty) (e: XCC.cexp t [a; b] c { XC.check_all PM.check_mode_unknown e }): stream t a -> stream t b -> stream t c =
  let e' = XCC.bless e in
  stream_of_exp2 e'

let stream_of_checked3 (#t: table) (#a #b #c #d: t.ty) (e: XCC.cexp t [a; b; c] d { XC.check_all PM.check_mode_unknown e }): stream t a -> stream t b -> stream t c -> stream t d =
  let e' = XCC.bless e in
  stream_of_exp3 e'


let system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (e: XCC.cexp t c a): prop =
  SI.induct1 (SX.system_of_exp e)

let system_induct_k (#t: table) (#c: context t) (#a: t.ty) (k: nat) (e: XCC.cexp t c a): prop =
  SI.induct_k k (SX.system_of_exp e)

let lemma_check_system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (e: XCC.cexp t c a):
  Lemma (requires (system_induct_k1 e))
        (ensures  (XC.check_all PM.check_mode_unknown e))
        [SMTPat (system_induct_k1 e)]
        =
    // TODO:ADMIT: see note CAUSALITY-ADMIT
    assume (Pipit.Exp.Causality.causal e);
    SI.induct1_sound_all (SX.system_of_exp e);
    SXCE.entailment_all e

let lemma_check_system_induct_k (#t: table) (#c: context t) (#a: t.ty) (k: nat) (e: XCC.cexp t c a):
  Lemma (requires (system_induct_k k e))
        (ensures  (XC.check_all PM.check_mode_unknown e))
        [SMTPat (system_induct_k k e)]
        =
    // TODO:ADMIT: induction is sound
    admit ()

let lemma_check_contract_system_induct_k1' (#t: table) (#c: context t) (#a: t.ty) (r: XCC.cexp t c t.propty) (g: XCC.cexp t (a :: c) t.propty) (b: XCC.cexp t c a):
  Lemma (requires (contract_system_induct_k1' r g b))
        (ensures  (XC.contract_valid r g b))
        [SMTPat (contract_system_induct_k1' r g b)]
        =
    // TODO:ADMIT: see note: CAUSALITY-ADMIT
    assume (Pipit.Exp.Causality.causal r);
    assume (Pipit.Exp.Causality.causal g);
    assume (Pipit.Exp.Causality.causal b);
    SI.induct1_sound_all (SX.system_of_contract r g b);
    SXCE.entailment_contract_all r g b

(***
  Note: CAUSALITY-ADMIT:
    We currently assume causality in the proof of check-correctness, as the
    proofs of correctness only apply to causal expressions.
    However, to check if an expression is causal we need to descend into the
    whole program. This eagerness is problematic when we want to do compositional
    proofs where we know that a sub-expression satisfies some contract, but do
    not know its exact contents. Consider the FIR example, which takes a
    non-streaming list of constant values, and recursively builds an FIR filter:

    > let rec fir (coeffs: list real) (input: stream real): stream real =
    >   match coeffs with
    >   | [] -> zero
    >   | c :: coeffs' -> (input * c) + fir coeffs' (0.0R `fby` input)

    In the recursive construction step, we can't eagerly evaluate the
    subexpression `fir coeffs'` to check whether it is causal, because we
    don't have a concrete value for `coeffs'`.  Requiring causality here makes
    it difficult to prove properties about these kinds of recursive programs.

    This assumption isn't a huge problem in practice, as the code generation
    requires causality. By the time we check the top-level expression, we will
    have a concrete value for coeffs, so we can check the concrete expression.

    In the future, we hope to solve this by enforcing causality at an earlier
    stage in the source langugage, but this requires some changes.

 ***)