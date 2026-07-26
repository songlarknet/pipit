module Pipit.Test.Node

module PR  = Pipit.Core.Exp.Prim
module PP  = Pipit.Core.Exp.Pure
module PES = Pipit.Core.Exp.Source
module S   = Pipit.Core.Source.Stream
module EB  = Pipit.Core.Example.Bool
module A   = Pipit.Core.Exp.Anf

let btrue:  PP.pterm = PP.PValue (PR.VBool true)
let bfalse: PP.pterm = PP.PValue (PR.VBool false)

let src: S.stream [EB.bool_ty] =
  let (o1, o2) =
    S.unzip2 #EB.bool_ty #[EB.bool_ty]
      (S.node #[EB.bool_ty; EB.bool_ty] #[EB.bool_ty; EB.bool_ty]
        "ctrl" (S.zip2 (S.const btrue) (S.const bfalse)))
  in
  S.liftP PR.PAnd (S.zip2 o1 o2)

let term: PES.term = S.exp_of_stream src

let capp: PES.term =
  PES.XNode "ctrl" [PES.XPure btrue; PES.XPure bfalse]

let o_proj (i: nat) : PES.term =
  PES.XLet [EB.bool_ty; EB.bool_ty] capp (PES.XTuple [PES.XProj i (PES.XBVar 0)])

let expected: PES.term =
  PES.XLet [EB.bool_ty; EB.bool_ty]
    (PES.XLet [EB.bool_ty] (o_proj 0)
      (PES.XLet [EB.bool_ty] (o_proj 1)
        (PES.XTuple [PES.XBVar 1; PES.XBVar 0])))
    (PES.XTuple [PES.XPrim PR.PAnd (PES.XTuple [PES.XProj 0 (PES.XBVar 0); PES.XProj 1 (PES.XBVar 0)])])

let node_lowers_ok (): Lemma (term == expected) =
  assert_norm (term == expected)

let node_typechecks (): Lemma (PES.infer EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty]) =
  assert_norm (PES.infer EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty])

let anf_expected: A.cont =
  A.CLetNode "ctrl" [A.APure btrue; A.APure bfalse] [PR.TBool; PR.TBool]
    (A.CLet PR.TBool (A.RPureApp PR.PAnd [A.AVar 0; A.AVar 1])
      (A.CRet [A.AVar 2]))

let anf_shares_node (): Lemma (A.to_anf EB.benv term == Some anf_expected) =
  assert_norm (A.to_anf EB.benv term == Some anf_expected)
