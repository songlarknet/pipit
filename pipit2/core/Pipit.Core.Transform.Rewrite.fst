module Pipit.Core.Transform.Rewrite

module PES = Pipit.Core.Exp.Source

let rec rewrite (step: PES.term -> PES.term) (e: PES.term): Tot PES.term (decreases e) =
  let e': PES.term =
    match e with
    | PES.XPure _           -> e
    | PES.XVar _            -> e
    | PES.XBVar _           -> e
    | PES.XFby v0s es       -> PES.XFby v0s (rewrite_args step es)
    | PES.XPrim h args      -> PES.XPrim h (rewrite_args step args)
    | PES.XTuple es         -> PES.XTuple (rewrite_args step es)
    | PES.XNode nm args     -> PES.XNode nm (rewrite_args step args)
    | PES.XProj j b         -> PES.XProj j (rewrite step b)
    | PES.XMu tys body      -> PES.XMu tys (rewrite step body)
    | PES.XLet tys rhs bod  -> PES.XLet tys (rewrite step rhs) (rewrite step bod)
    | PES.XContract s r g i -> PES.XContract s (rewrite step r) (rewrite step g) (rewrite step i)
    | PES.XCheck s b        -> PES.XCheck s (rewrite step b)
  in
  step e'
and rewrite_args (step: PES.term -> PES.term) (args: list PES.term)
: Tot (list PES.term) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> rewrite step a :: rewrite_args step tl
