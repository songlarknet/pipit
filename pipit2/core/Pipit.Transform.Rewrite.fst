(* Pipit.Transform.Rewrite -- an unverified, environment-free rewrite driver: a
   single bottom-up pass applying a local `step` at every `sterm` node. Design
   notes and rationale: see Pipit.Transform.Rewrite.md. *)
module Pipit.Transform.Rewrite

module PES = Pipit.Exp.Source

let rec rewrite (step: PES.sterm -> PES.sterm) (e: PES.sterm): Tot PES.sterm (decreases e) =
  let e': PES.sterm =
    match e with
    | PES.SPure _         -> e
    | PES.SVar _          -> e
    | PES.SBVar _         -> e
    | PES.SFby v b        -> PES.SFby v (rewrite step b)
    | PES.SPureApp h args -> PES.SPureApp h (rewrite_args step args)
  in
  step e'
and rewrite_args (step: PES.sterm -> PES.sterm) (args: list PES.sterm)
: Tot (list PES.sterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> rewrite step a :: rewrite_args step tl

(* Traverse the tuple layer, rewriting every `sterm` leaf. *)
let rec rewrite_t (step: PES.sterm -> PES.sterm) (t: PES.tterm): Tot PES.tterm (decreases t) =
  match t with
  | PES.TTuple es          -> PES.TTuple (rewrite_args step es)
  | PES.TStreamApp nm args -> PES.TStreamApp nm (rewrite_args step args)
  | PES.TRec tys body      -> PES.TRec tys (rewrite_t step body)
  | PES.TLet tys rhs bod   -> PES.TLet tys (rewrite_t step rhs) (rewrite_t step bod)
