module Pipit.System.Exp.Check.Ind

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

module SXCA = Pipit.System.Exp.Check.Assumptions
module SXCO = Pipit.System.Exp.Check.Obligations

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties
module SI  = Pipit.System.Ind

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality

module PM = Pipit.Prop.Metadata

module T    = FStar.Tactics

#push-options "--split_queries always"

let check_invariant_all
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { XC.causal e })
  (mode: PM.check_mode):
    Tot prop =
  forall (rows: list (row c)).
    check_invariant rows e mode

let rec induct1_sound
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (row1: row c)
  (e: exp t c a { XC.causal e }):
  Pure
    (SB.step_result (SX.state_of_exp e) (t.ty_sem a))
    (requires (
      check_invariant_all e PM.check_mode_valid /\
      SI.induct1 (SX.system_of_exp e)
    ))
    (ensures (fun stp ->
      check_invariant (row1 :: rows) e PM.check_mode_unknown /\
      SXP.system_of_exp_invariant (row1 :: rows) e stp.s /\
      SB.option_prop_sem stp.chck.assumptions /\
      SB.option_prop_sem stp.chck.obligations /\
      (exists s. stp == (SX.system_of_exp e).step row1 (SXP.step_oracle (row1 :: rows) e) s)
    ))
  =
    match rows with
    | [] ->
      SXP.invariant_init e;
      check_init e PM.check_mode_unknown;
      let s0 = (SX.system_of_exp e).init in
      let stp = eval_step rows row1 e s0 in
      SXCA.check_step_asm rows row1 e s0;
      SXCO.check_step_obl rows row1 e s0;
      stp
    | row1' :: rows' ->
      let stp0 = induct1_sound rows' row1' e in
      let stp  = eval_step rows row1 e stp0.s in
      assert (check_invariant (row1 :: rows) e PM.check_mode_valid);
      assert (check_invariant          rows  e PM.check_mode_unknown);
      SXCA.check_step_asm rows row1 e stp0.s;
      SXCO.check_step_obl rows row1 e stp0.s;
      stp

let induct1_sound_all
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      check_invariant_all e PM.check_mode_valid /\
      SI.induct1 (SX.system_of_exp e)
    ))
    (ensures (
      check_invariant_all e PM.check_mode_unknown
    ))
  =
    introduce forall (rows: list (row c)). check_invariant rows e PM.check_mode_unknown
    with match rows with
      | [] -> check_init e PM.check_mode_unknown
      | row1 :: rows ->
        let stp = induct1_sound rows row1 e in
        ()

//TODO: k-induction soundness