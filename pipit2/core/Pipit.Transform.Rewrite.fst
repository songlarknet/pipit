(* Pipit.Transform.Rewrite -- an unverified, environment-free rewrite driver: a
   single bottom-up pass applying a local `step` at every `sterm` node. Design
   notes and rationale: see Pipit.Transform.Rewrite.md. *)
module Pipit.Transform.Rewrite

module PEB = Pipit.Exp.Base

let rec rewrite (step: PEB.sterm -> PEB.sterm) (e: PEB.sterm): Tot PEB.sterm (decreases e) =
  let e': PEB.sterm =
    match e with
    | PEB.SPure _         -> e
    | PEB.SVar _          -> e
    | PEB.SBVar _         -> e
    | PEB.SFby v b        -> PEB.SFby v (rewrite step b)
    | PEB.SPureApp h args -> PEB.SPureApp h (rewrite_args step args)
  in
  step e'
and rewrite_args (step: PEB.sterm -> PEB.sterm) (args: list PEB.sterm)
: Tot (list PEB.sterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> rewrite step a :: rewrite_args step tl

(* Traverse the tuple layer, rewriting every `sterm` leaf. *)
let rec rewrite_t (step: PEB.sterm -> PEB.sterm) (t: PEB.tterm): Tot PEB.tterm (decreases t) =
  match t with
  | PEB.TTuple es          -> PEB.TTuple (rewrite_args step es)
  | PEB.TStreamApp nm args -> PEB.TStreamApp nm (rewrite_args step args)
  | PEB.TRec tys body      -> PEB.TRec tys (rewrite_t step body)
  | PEB.TLet tys rhs bod   -> PEB.TLet tys (rewrite_t step rhs) (rewrite_t step bod)
