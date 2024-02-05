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

type contract (t: table) (c: context t) (a: t.ty) (rely: XCC.cexp t c t.propty) (guar: XCC.cexp t (a :: c) t.propty) =
  impl: XCC.cexp t c a { XC.contract_valid rely guar impl }

let contract_of_exp1 (#t: table) (#a #b: t.ty) (r: XCC.cexp t [a] t.propty) (g: XCC.cexp t [b; a] t.propty) (i: XCC.cexp t [a] b  { XC.contract_valid r g i }): contract t [a] b r g = i

let contract_system_induct_k1' (#t: table) (#c: context t) (#a: t.ty) (r: XCC.cexp t c t.propty) (g: XCC.cexp t (a :: c) t.propty) (i: XCC.cexp t c a): prop =
  // Pipit.Exp.Causality.causal r /\
  // Pipit.Exp.Causality.causal g /\
  // Pipit.Exp.Causality.causal i /\
  SI.induct1 (SX.system_of_contract r g i)

let stream_of_contract1 (#t: table) (#a #b: t.ty) (#r: XCC.cexp t [a] t.propty) (#g: XCC.cexp t [b; a] t.propty) (contr: contract t [a] b r g): stream t a -> stream t b =
  // let rely = XCC.bless r in
  let rely = r in
  let guar = XCC.bless g in
  let impl = XCC.bless contr in
  let e = XContract PM.PSUnknown rely guar impl in
  // TODO:ADMIT: bless is sealed
  assume (XC.sealed false impl);
  assume (XC.sealed false guar);
  // TODO:ADMIT: requires contract_check
  assume (XC.contract_valid r g contr ==> XC.check_all PM.check_mode_valid e);
  stream_of_exp1 e

// let stream_of_contract2 (#t: table) (#a #b #c: t.ty) (contr: _contract t [a; b] c { XC.contract_valid contr.rely contr.guar contr.impl }): stream t a -> stream t b -> stream t c =
//   let rely = XCC.bless contr.rely in
//   let guar = XCC.bless contr.guar in
//   let impl = XCC.bless contr.impl in
//   let e = XContract PM.PSUnknown rely guar impl in
//   // TODO:ADMIT: requires contract_check
//   assume (XC.check_all PM.check_mode_valid e);
//   stream_of_exp2 e


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
    // TODO:ADMIT: induction is sound
    admit ()

let lemma_check_system_induct_k (#t: table) (#c: context t) (#a: t.ty) (k: nat) (e: XCC.cexp t c a):
  Lemma (requires (system_induct_k k e))
        (ensures  (XC.check_all PM.check_mode_unknown e))
        [SMTPat (system_induct_k k e)]
        =
    // TODO:ADMIT: induction is sound
    admit ()

let lemma_check_contract_system_induct_k1' (#t: table) (#c: context t) (#a: t.ty) (r: XCC.cexp t c t.propty) (g: XCC.cexp t (a :: c) t.propty) (i: XCC.cexp t c a):
  Lemma (requires (contract_system_induct_k1' r g i))
        (ensures  (XC.contract_valid r g i))
        [SMTPat (contract_system_induct_k1' r g i)]
        =
    // TODO:ADMIT: induction is sound
    admit ()
