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

module PEB = Pipit.Exp.Base

(* An empty signature environment suffices: the equations use only `SFby` over
   integer literals, so no primitive / node lookups occur. *)
let env : PEB.sigenv = { PEB.prims = []; nodes = [] }

let i0 : PEB.pterm = PEB.PLit (PEB.LInt 0)
let i1 : PEB.pterm = PEB.PLit (PEB.LInt 1)

(* `a = 0 fby b  and  b = 1 fby a`, as a two-member recursion group (a tuple). *)
let rec_ab : PEB.tterm =
  PEB.TRec [PEB.TInt; PEB.TInt]
    (PEB.TTuple
      [ PEB.SFby i0 (PEB.SBVar 1)     (* member 0 = a = 0 fby b *)
      ; PEB.SFby i1 (PEB.SBVar 0) ])  (* member 1 = b = 1 fby a *)

(* The group is a tuple of streams: `infer_t` gives its two component types. *)
let _ = assert_norm (PEB.infer_t env [] rec_ab == Some [PEB.TInt; PEB.TInt])

(* A single component is read back with the *projection idiom*
   `TLet tys tt (TTuple [SBVar i])` -- there is no `SProject` former -- and each
   in-range projection is a well-typed (width-1) integer stream. *)
let proj (i: nat) : PEB.tterm =
  PEB.TLet [PEB.TInt; PEB.TInt] rec_ab (PEB.TTuple [PEB.SBVar i])

let _ = assert_norm (PEB.infer_t env [] (proj 0) == Some [PEB.TInt])
let _ = assert_norm (PEB.infer_t env [] (proj 1) == Some [PEB.TInt])

(* An out-of-range projection is ill-typed. *)
let _ = assert_norm (PEB.infer_t env [] (proj 2) == None)

(* ----- close / open shift by the group arity (n binders at once) --------- *)

let x : PEB.svar = { PEB.svname = 0; svty = PEB.TInt }

(* Member 0 refers to a *free* outer variable `x`; the group binds two members,
   so closing `x` must land it at de Bruijn index 0 + 2 = 2. *)
let grp_open : PEB.tterm =
  PEB.TRec [PEB.TInt; PEB.TInt]
    (PEB.TTuple
      [ PEB.SFby i0 (PEB.SVar x)
      ; PEB.SFby i1 (PEB.SBVar 0) ])

let grp_closed : PEB.tterm =
  PEB.TRec [PEB.TInt; PEB.TInt]
    (PEB.TTuple
      [ PEB.SFby i0 (PEB.SBVar 2)
      ; PEB.SFby i1 (PEB.SBVar 0) ])

let _ = assert_norm (PEB.close_rec_t 0 x grp_open == grp_closed)
let _ = assert_norm (PEB.open_rec_t 0 (PEB.SVar x) grp_closed == grp_open)
