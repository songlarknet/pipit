(* Pipit.Test.Rec -- n-ary mutual recursion (`TRec`) type-checks and its
   binders close/open correctly. The flagship example is the roadmap's mutual
   pair `a = 0 fby b  and  b = 1 fby a` (see ../doc/roadmap/next-project-plan.md,
   M0): a two-member `TRec` where member 0 is `a`, member 1 is `b`, and each
   equation refers to the other member through a de Bruijn binder (`SBVar 1` =
   `b` inside `a`'s equation, `SBVar 0` = `a` inside `b`'s equation).

   ANF lowering of recursion is deliberately *not* exercised here: `to_anf`
   returns `None` on `TRec` (a dedicated follow-up slice, co-designed with the
   transition-system view). This slice validates syntax + checker + close/open. *)
module Pipit.Test.Rec

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source

(* An empty signature environment suffices: the equations use only `SFby` over
   integer values, so no node lookups occur. *)
let env : PES.sigenv = { PES.nodes = [] }

let i0 : PP.pterm = PP.PValue (PR.VInt 0)
let i1 : PP.pterm = PP.PValue (PR.VInt 1)

(* `a = 0 fby b  and  b = 1 fby a`, as a two-member recursion group (a tuple). *)
let rec_ab : PES.tterm =
  PES.TRec [PR.TInt; PR.TInt]
    (PES.TTuple
      [ PES.SFby i0 (PES.SBVar 1)     (* member 0 = a = 0 fby b *)
      ; PES.SFby i1 (PES.SBVar 0) ])  (* member 1 = b = 1 fby a *)

(* The group is a tuple of streams: `infer_t` gives its two component types. *)
let _ = assert_norm (PES.infer_t env [] rec_ab == Some [PR.TInt; PR.TInt])

(* A single component is read back with the *projection idiom*
   `TLet tys tt (TTuple [SBVar i])` -- there is no `SProject` former -- and each
   in-range projection is a well-typed (width-1) integer stream. *)
let proj (i: nat) : PES.tterm =
  PES.TLet [PR.TInt; PR.TInt] rec_ab (PES.TTuple [PES.SBVar i])

let _ = assert_norm (PES.infer_t env [] (proj 0) == Some [PR.TInt])
let _ = assert_norm (PES.infer_t env [] (proj 1) == Some [PR.TInt])

(* An out-of-range projection is ill-typed. *)
let _ = assert_norm (PES.infer_t env [] (proj 2) == None)

(* ----- close / open shift by the group arity (n binders at once) --------- *)

let x : PES.svar = { PES.svname = 0; svty = PR.TInt }

(* Member 0 refers to a *free* outer variable `x`; the group binds two members,
   so closing `x` must land it at de Bruijn index 0 + 2 = 2. *)
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
