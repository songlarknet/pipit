(* Pipit.Transform.Rewrite -- an unverified, environment-free rewrite driver.

   This is the "untrusted transform" half of the story (see
   ../doc/roadmap/next-project-plan.md, milestone M1'): a driver applies a local
   `step` at every node and produces a new `sterm`. It carries *no* soundness
   proof -- establishing `stream_eq e (rewrite step e)` is a separate obligation
   (per-rule congruence lemmas, deferred). Being pure syntax -> syntax, it needs
   *no* environment at all (the checker needs signatures, the evaluator needs
   the dynamic interpretation, the transform needs neither).

   `rewrite step` is a single bottom-up pass: it rewrites every child first,
   then applies `step` once at the (rebuilt) node. A `step` that only matches a
   fixed shape and is the identity elsewhere therefore fires everywhere that
   shape occurs, including under binders -- exactly the congruence behaviour a
   rule-based optimiser wants. *)
module Pipit.Transform.Rewrite

module PEB = Pipit.Exp.Base

(* Apply `step` once at every `sterm` node, bottom-up. `rewrite` (single streams)
   never descends into a `tterm`; `rewrite_t` traverses the tuple layer and calls
   back into `rewrite` at the `sterm` leaves. *)
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

(* Traverse the tuple layer, rewriting every `sterm` leaf. Tuple nodes carry no
   `step` of their own -- the rule acts on single streams. *)
let rec rewrite_t (step: PEB.sterm -> PEB.sterm) (t: PEB.tterm): Tot PEB.tterm (decreases t) =
  match t with
  | PEB.TTuple es          -> PEB.TTuple (rewrite_args step es)
  | PEB.TStreamApp nm args -> PEB.TStreamApp nm (rewrite_args step args)
  | PEB.TRec tys body      -> PEB.TRec tys (rewrite_t step body)
  | PEB.TLet tys rhs bod   -> PEB.TLet tys (rewrite_t step rhs) (rewrite_t step bod)
