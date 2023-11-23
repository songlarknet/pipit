module Network.TTCan.Extract

module Top = Network.TTCan.CycleTime

module SugarBase = Pipit.Sugar.Base
module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.LowStar

module Tac = FStar.Tactics

[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Network.TTCan"]))]
noextract
let expr = SugarBase.exp_of_stream2 Top.top

[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Network.TTCan"]))]
type state = XX.state_of_exp expr

type result = Top.ntu

[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Network.TTCan"]))]
noextract
inline_for_extraction
let system: XX.esystem (Top.ntu & (bool & unit)) state result =
  assert_norm (XX.extractable expr);
  XX.exec_of_exp expr

[@@(Tac.postprocess_with (XL.tac_extract ["Network.TTCan"]))]
let reset = XL.mk_reset system

[@@(Tac.postprocess_with (XL.tac_extract ["Network.TTCan"]))]
let step (local_time: Top.ntu) (reset_ck: bool) = XL.mk_step system (local_time, (reset_ck, ()))