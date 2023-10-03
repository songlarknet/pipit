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

noeq
type _contract (t: table) (c: context t) (a: t.ty) = {
  rely: XCC.cexp t       c  t.propty;
  guar: XCC.cexp t (a :: c) t.propty;
  impl: XCC.cexp t       c         a;
}

let contract_of_stream1 (#t: table) (#a #b: t.ty) (f: s t a -> Base._contract t b) : _contract t [a] b = {
  rely = exp_of_stream1 (fun a -> (f a).rely);
  guar = exp_of_stream2 (fun b a -> (f a).guar b);
  impl = exp_of_stream1 (fun a -> (f a).impl);
}

let contract_of_stream2 (#t: table) (#a #b #c: t.ty) (f: s t a -> s t b -> Base._contract t c) : _contract t [a; b] c = {
  rely = exp_of_stream2 (fun a b -> (f a b).rely);
  guar = exp_of_stream3 (fun c a b -> (f a b).guar c);
  impl = exp_of_stream2 (fun a b -> (f a b).impl);
}


let contract_system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (contr: _contract t c a): prop =
  Pipit.Exp.Causality.causal contr.rely /\
  Pipit.Exp.Causality.causal contr.guar /\
  Pipit.Exp.Causality.causal contr.impl /\
  SI.induct1 (SX.system_of_contract contr.rely contr.guar contr.impl)

let contract_system_induct_k (#t: table) (#c: context t) (#a: t.ty) (k: nat) (contr: _contract t c a): prop =
  Pipit.Exp.Causality.causal contr.rely /\
  Pipit.Exp.Causality.causal contr.guar /\
  Pipit.Exp.Causality.causal contr.impl /\
  SI.induct_k k (SX.system_of_contract contr.rely contr.guar contr.impl)


let stream_of_contract1 (#t: table) (#a #b: t.ty) (contr: _contract t [a] b { XC.check_contract_definition PM.check_mode_all contr.rely contr.guar contr.impl }): s t a -> s t b =
  let rely = XC.bless contr.rely in
  let guar = XC.bless contr.guar in
  let impl = XC.bless contr.impl in
  let e = XContract PM.PSUnknown rely guar impl in
  // TODO:ADMIT: requires contract_check
  assume (XC.check' PM.check_mode_valid e);
  stream_of_exp1 e

let stream_of_contract2 (#t: table) (#a #b #c: t.ty) (contr: _contract t [a; b] c { XC.check_contract_definition PM.check_mode_all contr.rely contr.guar contr.impl }): s t a -> s t b -> s t c =
  let rely = XC.bless contr.rely in
  let guar = XC.bless contr.guar in
  let impl = XC.bless contr.impl in
  let e = XContract PM.PSUnknown rely guar impl in
  // TODO:ADMIT: requires contract_check
  assume (XC.check' PM.check_mode_valid e);
  stream_of_exp2 e


let exp_of_stream0 (#t: table) (#ty: t.ty) (e: s t ty) : XCC.cexp t [] ty = exp_of_stream0 e
let exp_of_stream1 (#t: table) (#a #b: t.ty) (f: s t a -> s t b) : XCC.cexp t [a] b = exp_of_stream1 f
let exp_of_stream2 (#t: table) (#a #b #c: t.ty) (f: s t a -> s t b -> s t c) : XCC.cexp t [a; b] c = exp_of_stream2 f
let exp_of_stream3 (#t: table) (#a #b #c #d: t.ty) (f: s t a -> s t b -> s t c -> s t d) : XCC.cexp t [a; b; c] d = exp_of_stream3 f


let stream_of_checked0 (#t: table) (#a: t.ty) (e: exp t [] a { XC.check' PM.check_mode_all e }): s t a =
  let e' = XC.bless e in
  stream_of_exp0 e'

let stream_of_checked1 (#t: table) (#a #b: t.ty) (e: exp t [a] b { XC.check' PM.check_mode_all e }): s t a -> s t b =
  let e' = XC.bless e in
  stream_of_exp1 e'

let stream_of_checked2 (#t: table) (#a #b #c: t.ty) (e: exp t [a; b] c { XC.check' PM.check_mode_all e }): s t a -> s t b -> s t c =
  let e' = XC.bless e in
  stream_of_exp2 e'

let stream_of_checked3 (#t: table) (#a #b #c #d: t.ty) (e: exp t [a; b; c] d { XC.check' PM.check_mode_all e }): s t a -> s t b -> s t c -> s t d =
  let e' = XC.bless e in
  stream_of_exp3 e'


let system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (e: XCC.cexp t c a): prop =
  Pipit.Exp.Causality.causal e /\ SI.induct1 (SX.system_of_exp e)

let system_induct_k (#t: table) (#c: context t) (#a: t.ty) (k: nat) (e: XCC.cexp t c a): prop =
  Pipit.Exp.Causality.causal e /\ SI.induct_k k (SX.system_of_exp e)

let lemma_check_system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (e: XCC.cexp t c a):
  Lemma (requires (system_induct_k1 e))
        (ensures  (XC.check' PM.check_mode_all e))
        [SMTPat (system_induct_k1 e)]
        =
    // TODO:ADMIT: induction is sound
    admit ()

let lemma_check_system_induct_k (#t: table) (#c: context t) (#a: t.ty) (k: nat) (e: XCC.cexp t c a):
  Lemma (requires (system_induct_k k e))
        (ensures  (XC.check' PM.check_mode_all e))
        [SMTPat (system_induct_k k e)]
        =
    // TODO:ADMIT: induction is sound
    admit ()

let lemma_check_contract_system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (contr: _contract t c a):
  Lemma (requires (contract_system_induct_k1 contr))
        (ensures  (XC.check_contract_definition PM.check_mode_all contr.rely contr.guar contr.impl))
        [SMTPat (contract_system_induct_k1 contr)]
        =
    // TODO:ADMIT: induction is sound
    admit ()
