module Pipit.Test.Rec

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source

let env : PES.sigenv = { PES.nodes = [] }

let i0 : PP.pterm = PP.PValue (PR.VInt 0)
let i1 : PP.pterm = PP.PValue (PR.VInt 1)

(* `a = 0 fby b  and  b = 1 fby a` *)
let rec_ab : PES.tterm =
  PES.TRec [PR.TInt; PR.TInt]
    (PES.TTuple
      [ PES.SFby i0 (PES.SBVar 1)
      ; PES.SFby i1 (PES.SBVar 0) ])

let _ = assert_norm (PES.infer_t env [] rec_ab == Some [PR.TInt; PR.TInt])

let proj (i: nat) : PES.tterm =
  PES.TLet [PR.TInt; PR.TInt] rec_ab (PES.TTuple [PES.SBVar i])

let _ = assert_norm (PES.infer_t env [] (proj 0) == Some [PR.TInt])
let _ = assert_norm (PES.infer_t env [] (proj 1) == Some [PR.TInt])

let _ = assert_norm (PES.infer_t env [] (proj 2) == None)

let x : PES.svar = { PES.svname = 0; svty = PR.TInt }

let grp_open : PES.tterm =
  PES.TRec [PR.TInt; PR.TInt]
    (PES.TTuple
      [ PES.SFby i0 (PES.SVar x)
      ; PES.SFby i1 (PES.SBVar 0) ])

let grp_closed : PES.tterm =
  PES.TRec [PR.TInt; PR.TInt]
    (PES.TTuple
      [ PES.SFby i0 (PES.SBVar 2)
      ; PES.SFby i1 (PES.SBVar 0) ])

let _ = assert_norm (PES.close_rec_t 0 x grp_open == grp_closed)
let _ = assert_norm (PES.open_rec_t 0 (PES.SVar x) grp_closed == grp_open)
