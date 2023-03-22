(* Manual translation example *)
module Pipit.Exec.Example

module E = Pipit.Exp.Base
module XB = Pipit.Exec.Base
module XL = Pipit.Exec.LowStar
module T = Pipit.Check.Example.Top

module Tac = FStar.Tactics

[@@(Tac.postprocess_with XL.tac_post)]
let reset = XL.mk_reset (XB.exec_of_exp (T.count_when (E.XVar 0)) 1)

[@@(Tac.postprocess_with XL.tac_post)]
let step = XL.mk_step (XB.exec_of_exp (T.count_when (E.XVar 0)) 1)
