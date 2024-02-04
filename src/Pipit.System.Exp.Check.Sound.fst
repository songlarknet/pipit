module Pipit.System.Exp.Check.Sound

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

open FStar.Squash

module SXCA = Pipit.System.Exp.Check.Assumptions
module SXCO = Pipit.System.Exp.Check.Obligations

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties
module SI  = Pipit.System.Ind

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality
module XK  = Pipit.Exp.Checked.Base
module XKS = Pipit.Exp.Checked.Subst

module PM = Pipit.Prop.Metadata

module T    = FStar.Tactics

#push-options "--split_queries always"

let check_invariant_all
  (#t: table) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (e: exp t c a { XC.causal e }):
    Tot prop =
  forall (rows: list (row c)).
    check_invariant rows e mode


let check_all_Fby
  (#t: table) (#c: context t) (#a: t.ty)
  (v: t.ty_sem a)
  (e: exp t c a { XC.causal e })
  (mode: PM.check_mode):
  Lemma
    (requires (
      XK.check_all mode (XFby v e)
    ))
    (ensures (
      XK.check_all mode e
    ))
  =
  introduce forall (rows: list (row c)). XK.check_prop mode rows e
  with
    match rows with
    | [] ->
      let k: XK.check mode rows e = checkK_init e mode in
      let kk: squash (XK.check mode rows e) = return_squash k in
      // assert (XK.check_prop mode rows e);
      () // check_init e mode
    | r::_ ->
      assert (XK.check_prop mode (r::rows) (XFby v e));
      let hC: squash (XK.check mode (r::rows) (XFby v e)) = () in
      let hC': squash (XK.check mode rows e) =
        bind_squash hC (fun hC ->
        match hC with
        | XK.CkFbyS _ _ _ _ _ -> ()
        | _ -> false_elim ()
      ) in
      ()


let rec check_invariant_of_check_all
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  (mode: PM.check_mode):
  Lemma
    (requires (
      XK.check_all mode e
    ))
    (ensures (
      check_invariant rows e mode
    ))
    (decreases e)
    =
  match e with
  | XBase _ -> ()
  | XFby v e1 ->
    check_all_Fby v e1 mode;
    check_invariant_of_check_all rows e1 mode
  | XMu e1 ->
    admit ()
  | _ -> admit ()

let rec check_all_of_check_unknown
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      XK.check_all PM.check_mode_valid e /\
      check_invariant_all PM.check_mode_unknown e
    ))
    (ensures (
      XK.check PM.check_mode_unknown rows e
    ))
    (decreases e)
    =
  match e with
  | XBase b -> return_squash (XK.CkBase #PM.check_mode_unknown rows b)
  // | XFby v e1 ->
  //   check_all_Fby v e1 PM.check_mode_valid;
  //   check_all_of_check_unknown rows e1
    // check_invariant_of_check_all rows e1 mode
  | XMu e1 ->
    admit ()
  | _ -> admit ()

