module Pipit.Sugar.Contract

open Pipit.Prim.Table

open Pipit.Exp.Base

open Pipit.Sugar.Base
module Base = Pipit.Sugar.Base
module Check = Pipit.Sugar.Check

module XC  = Pipit.Exp.Checked.Base
module XCC = Pipit.Exp.Checked.Compound
module PM  = Pipit.Prop.Metadata

// module SB  = Pipit.System.Base
module SI  = Pipit.System.Ind
module SX  = Pipit.System.Exp

noeq
type contract_struct (r g b: Type) = {
  rely: r;
  guar: g;
  body: b;
}

(* Unchecked contract of expressions *)
noeq
type contract (t: table) (c: context t) (a: t.ty) =
  | Contract:
    (rely: XCC.cexp t c t.propty) ->
    (guar: XCC.cexp t (a :: c) t.propty) ->
    (body: XCC.cexp t c a) ->
    contract t c a

let contract_valid (#t: table) (#c: context t) (#a: t.ty) (ctr: contract t c a) =
  match ctr with
  | Contract r g b -> XC.check_contract_definition PM.check_mode_all r g b

let contract_of_stream1 (#t: table) (#a #b: t.ty) (c: contract_struct (stream t a -> stream t t.propty)  (stream t b -> stream t a -> stream t t.propty) (stream t a -> stream t b)): contract t [a] b =
  Contract
    (exp_of_stream1 c.rely)
    (exp_of_stream2 c.guar)
    (exp_of_stream1 c.body)

let system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (ctr: contract t c a): prop =
  match ctr with
  | Contract r g b -> SI.induct1 (SX.system_of_contract r g b)

let stream_of_contract1 (#t: table) (#a #b: t.ty) (ctr: contract t [a] b { contract_valid ctr }): stream t a -> stream t b =
  match ctr with
  | Contract rely guar body -> Check.stream_of_contract1 #t #_ #_ #rely #guar body

let lemma_check_system_induct_k1 (#t: table) (#c: context t) (#a: t.ty) (ctr: contract t c a):
  Lemma (requires (system_induct_k1 ctr))
        (ensures  (contract_valid ctr))
        [SMTPat (system_induct_k1 ctr)]
        =
    match ctr with
    | Contract rely guar body -> Check.lemma_check_contract_system_induct_k1' rely guar body
