(* Properties that hold on the translated system hold on the original semantics *)
module Pipit.System.Exp.Check.Entailment

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

module SXCA = Pipit.System.Exp.Check.Assumptions
module SXCC = Pipit.System.Exp.Check.Contracts
module SXCI = Pipit.System.Exp.Check.Invariants
module SXCO = Pipit.System.Exp.Check.Obligations

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties
module SI  = Pipit.System.Ind

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality
module XK  = Pipit.Exp.Checked.Base

module PM = Pipit.Prop.Metadata

module List = FStar.List.Tot
module T    = FStar.Tactics

#push-options "--split_queries always"

let rec entailment
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (row1: row c)
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      XK.check_all PM.check_mode_valid e /\
      XK.sealed true e /\
      SI.system_holds_all (SX.system_of_exp e)
    ))
    (ensures (
      let ios = inputs_with_oracles (row1 :: rows) e in
      let stp = SI.system_step_result (SX.system_of_exp e) ios in
      XK.check PM.check_mode_unknown (row1 :: rows) e /\
      check_invariant PM.check_mode_unknown (row1 :: rows) e /\
      SXP.system_of_exp_invariant (row1 :: rows) e stp.s /\
      SI.system_assumptions_sofar (SX.system_of_exp e) ios /\
      SB.option_prop_sem stp.chck.assumptions /\
      SB.option_prop_sem stp.chck.obligations
    ))
  =
    SXCI.check_invariant_of_check_base PM.check_mode_valid (row1 :: rows) e;
    let ios  = inputs_with_oracles (row1 :: rows) e in
    match rows with
    | [] ->
      SXP.invariant_init e;
      check_init PM.check_mode_unknown e;
      let s0 = (SX.system_of_exp e).init in
      let stp = eval_step rows row1 e s0 in
      SXCA.check_step_asm rows row1 e s0;
      assert (SI.system_assumptions_sofar (SX.system_of_exp e) ios);
      SXCO.check_step_obl rows row1 e s0;
      SXCI.check_base_unknown_of_check_invariant (row1 :: rows) e;
      ()
    | row1' :: rows' ->
      entailment rows' row1' e;
      let ios' = inputs_with_oracles rows e in
      let stp0 = SI.system_step_result (SX.system_of_exp e) ios' in
      let stp  = eval_step rows row1 e stp0.s in
      assert (check_invariant PM.check_mode_valid   (row1 :: rows) e);
      assert (check_invariant PM.check_mode_unknown          rows  e);
      SXCA.check_step_asm rows row1 e stp0.s;
      assert (check_invariant PM.check_mode_valid   (row1 :: rows) e);
      assert (check_invariant PM.check_mode_unknown          rows  e);
      assert (SB.option_prop_sem stp.chck.assumptions);
      assert (SI.system_assumptions_sofar (SX.system_of_exp e) ios);
      assert (SB.option_prop_sem stp.chck.obligations);
      SXCO.check_step_obl rows row1 e stp0.s;
      SXCI.check_base_unknown_of_check_invariant (row1 :: rows) e;
      ()


let entailment_all
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      XK.check_all PM.check_mode_valid e /\
      XK.sealed true e /\
      SI.system_holds_all (SX.system_of_exp e)
    ))
    (ensures (
      XK.check_all PM.check_mode_unknown e
    ))
  =
    introduce forall (rows: list (row c)). XK.check PM.check_mode_unknown rows e
    with match rows with
      | [] -> SXCI.check_base_nil PM.check_mode_unknown e
      | row1 :: rows ->
        let stp = entailment rows row1 e in
        ()

let entailment_contract
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c) { Cons? rows })
  (r: exp t       c  t.propty { XC.causal r })
  (g: exp t (a :: c) t.propty { XC.causal g })
  (b: exp t       c         a { XC.causal b }):
  Lemma
    (requires (
      XK.check_all PM.check_mode_valid r /\
      XK.check_all PM.check_mode_valid g /\
      XK.check_all PM.check_mode_valid b /\
      XK.sealed true r /\
      XK.sealed true g /\
      XK.sealed true b /\
      XB.bigstep_always rows r /\
      SI.system_holds_all (SX.system_of_contract r g b)
    ))
    (ensures (
      let vs = XC.lemma_bigsteps_total_vs rows b in
      XK.check PM.check_mode_unknown rows r /\
      XK.check PM.check_mode_unknown rows b /\
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) g /\
      XB.bigstep_always (CR.extend1 vs rows) g
    ))
    =
  let vs  = XC.lemma_bigsteps_total_vs rows b in
  let rows'=CR.extend1 vs rows in
  SXCI.check_invariant_of_check_base PM.check_mode_valid rows r;
  SXCI.check_invariant_of_check_base PM.check_mode_valid (CR.extend1 vs rows) g;
  SXCI.check_invariant_of_check_base PM.check_mode_valid rows b;

  assert (XB.bigstep_always rows r);
  assert (SI.system_holds_all (SX.system_of_contract r g b));

  SXCC.system_holds_exp_of_contract rows r g b;

  SXCI.check_base_unknown_of_check_invariant rows r;
  SXCI.check_base_unknown_of_check_invariant rows' g;
  SXCI.check_base_unknown_of_check_invariant rows b;
  ()

let entailment_contract_all
  (#t: table) (#c: context t) (#a: t.ty)
  (r: exp t       c  t.propty { XC.causal r })
  (g: exp t (a :: c) t.propty { XC.causal g })
  (b: exp t       c         a { XC.causal b }):
  Lemma
    (requires (
      XK.check_all PM.check_mode_valid r /\
      XK.check_all PM.check_mode_valid g /\
      XK.check_all PM.check_mode_valid b /\
      XK.sealed true r /\
      XK.sealed true g /\
      XK.sealed true b /\
      SI.system_holds_all (SX.system_of_contract r g b)
    ))
    (ensures (
      XK.contract_valid r g b
    ))
  =
    introduce
      forall (rows: list (row c)) (vs: list (t.ty_sem a) { XB.bigsteps_prop rows b vs }).
      XB.bigstep_always rows r ==>
      XK.check PM.check_mode_valid rows r ==>
      XK.check PM.check_mode_valid rows b ==>
      XK.check PM.check_mode_valid (CR.extend1 vs rows) g ==>
        (XK.check PM.check_mode_unknown rows b /\
        XK.check PM.check_mode_unknown (CR.extend1 vs rows) g /\
        XB.bigstep_always (CR.extend1 vs rows) g)
    with
      introduce 
        XB.bigstep_always rows r ==>
        (XK.check PM.check_mode_valid rows r ==>
        XK.check PM.check_mode_valid rows b ==>
        XK.check PM.check_mode_valid (CR.extend1 vs rows) g ==>
          (XK.check PM.check_mode_unknown rows b /\
          XK.check PM.check_mode_unknown (CR.extend1 vs rows) g /\
          XB.bigstep_always (CR.extend1 vs rows) g))
      with pf. (
        (match rows with
        | [] ->
          SXCI.check_base_nil PM.check_mode_unknown g;
          SXCI.check_base_nil PM.check_mode_unknown b
        | _ -> entailment_contract rows r g b);
        XB.bigsteps_deterministic_squash rows b vs (XC.lemma_bigsteps_total_vs rows b);
        ()
      )
