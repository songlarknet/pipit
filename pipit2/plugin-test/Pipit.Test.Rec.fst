module Pipit.Test.Rec

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source

let env : PES.sigenv = { PES.nodes = [] }

let i0 : PP.pterm = PP.PValue (PR.VInt 0)
let i1 : PP.pterm = PP.PValue (PR.VInt 1)

(* `a = 0 fby b  and  b = 1 fby a` *)
let rec_ab : PES.term =
  PES.XMu [PR.TInt; PR.TInt]
    (PES.XTuple
      [ PES.XFby i0 (PES.XProj 1 (PES.XBVar 0))
      ; PES.XFby i1 (PES.XProj 0 (PES.XBVar 0)) ])

let _ = assert_norm (PES.infer env [] rec_ab == Some [PR.TInt; PR.TInt])

let proj (i: nat) : PES.term =
  PES.XLet [PR.TInt; PR.TInt] rec_ab (PES.XTuple [PES.XProj i (PES.XBVar 0)])

let _ = assert_norm (PES.infer env [] (proj 0) == Some [PR.TInt])
let _ = assert_norm (PES.infer env [] (proj 1) == Some [PR.TInt])

let _ = assert_norm (PES.infer env [] (proj 2) == None)

let x : PES.svar = { PES.svname = 0; svty = [PR.TInt] }

let grp_open : PES.term =
  PES.XMu [PR.TInt; PR.TInt]
    (PES.XTuple
      [ PES.XFby i0 (PES.XVar x)
      ; PES.XFby i1 (PES.XProj 0 (PES.XBVar 0)) ])

let grp_closed : PES.term =
  PES.XMu [PR.TInt; PR.TInt]
    (PES.XTuple
      [ PES.XFby i0 (PES.XBVar 1)
      ; PES.XFby i1 (PES.XProj 0 (PES.XBVar 0)) ])

let _ = assert_norm (PES.close_rec 0 x grp_open == grp_closed)
let _ = assert_norm (PES.open_rec 0 (PES.XVar x) grp_closed == grp_open)
