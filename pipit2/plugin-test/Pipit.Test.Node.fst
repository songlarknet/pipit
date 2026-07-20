module Pipit.Test.Node

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source
module S   = Pipit.Source.Stream
module EB  = Pipit.Example.Bool
module A   = Pipit.Exp.Anf

let btrue:  PP.pterm = PP.PValue (PR.VBool true)
let bfalse: PP.pterm = PP.PValue (PR.VBool false)

let src: S.stream [EB.bool_ty] =
  let (o1, o2) =
    S.unzip2 #EB.bool_ty #[EB.bool_ty]
      (S.node #[EB.bool_ty; EB.bool_ty] #[EB.bool_ty; EB.bool_ty]
        "ctrl" (S.zip2 (S.const btrue) (S.const bfalse)))
  in
  S.liftP PR.PAnd (S.zip2 o1 o2)

let term: PES.tterm = S.exp_of_stream src

let capp: PES.tterm =
  PES.TStreamApp "ctrl" [PES.SPure btrue; PES.SPure bfalse]

let o_proj (i: nat) : PES.tterm =
  PES.TLet [EB.bool_ty; EB.bool_ty] capp (PES.TTuple [PES.SBVar i])

let expected: PES.tterm =
  PES.TLet [EB.bool_ty; EB.bool_ty]
    (PES.TLet [EB.bool_ty] (o_proj 0)
      (PES.TLet [EB.bool_ty] (o_proj 1)
        (PES.TTuple [PES.SBVar 1; PES.SBVar 0])))
    (PES.TTuple [PES.SPureApp PR.PAnd [PES.SBVar 0; PES.SBVar 1]])

let node_lowers_ok (): Lemma (term == expected) =
  assert_norm (term == expected)

let node_typechecks (): Lemma (PES.infer_t EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty]) =
  assert_norm (PES.infer_t EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty])

let anf_expected: A.cont =
  A.CLetNode "ctrl" [A.APure btrue; A.APure bfalse] [PR.TBool; PR.TBool]
    (A.CLet PR.TBool (A.RPureApp PR.PAnd [A.AVar 0; A.AVar 1])
      (A.CRet [A.AVar 2]))

let anf_shares_node (): Lemma (A.to_anf EB.benv term == Some anf_expected) =
  assert_norm (A.to_anf EB.benv term == Some anf_expected)
