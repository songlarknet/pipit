(* Properties about contract definitions *)
module Pipit.System.Exp.Check.Contracts

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

module SXCA = Pipit.System.Exp.Check.Assumptions
module SXCO = Pipit.System.Exp.Check.Obligations
module SXCI = Pipit.System.Exp.Check.Invariants

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

let rec contract_invariant_holds
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c) { Cons? rows })
  (r: exp t       c  t.propty { XC.causal r })
  (g: exp t (a :: c) t.propty { XC.causal g })
  (b: exp t       c         a { XC.causal b }):
  Lemma
    (ensures (
      let vs  = XC.lemma_bigsteps_total_vs rows b in
      let rows'=CR.extend1 vs rows in
      let t   = SX.system_of_contract r g b in
      let ios = inputs_with_oracles_contract_definition rows r g b in
      let stp = SI.system_step_result t ios in

      let iosr = inputs_with_oracles rows r in
      let stpr = SI.system_step_result (SX.system_of_exp r) iosr in

      let iosg = inputs_with_oracles rows' g in
      let stpg = SI.system_step_result (SX.system_of_exp g) iosg in

      let iosb = inputs_with_oracles rows b in
      let stpb = SI.system_step_result (SX.system_of_exp b) iosb in

      SXP.system_of_contract_invariant rows r g b stp.s /\
      stp.s == SB.type_join_tup stpr.s (SB.type_join_tup stpg.s stpb.s) /\
      (SB.option_prop_sem stp.chck.assumptions <==> (
        b2t stpr.v /\
        SB.option_prop_sem stpr.chck.assumptions /\
        SB.option_prop_sem stpg.chck.assumptions /\
        SB.option_prop_sem stpb.chck.assumptions)) /\
      (SB.option_prop_sem stp.chck.obligations <==> (
        b2t stpg.v /\
        SB.option_prop_sem stpr.chck.obligations /\
        SB.option_prop_sem stpg.chck.obligations /\
        SB.option_prop_sem stpb.chck.obligations)) /\
      (stpr.v == XC.lemma_bigstep_total_v rows r) /\
      (stpg.v == XC.lemma_bigstep_total_v rows' g) /\
      (stpb.v == XC.lemma_bigstep_total_v rows b) /\
      (stp.v  == XC.lemma_bigstep_total_v rows b)
    ))
  =
  // let vs  = XC.lemma_bigsteps_total_vs rows b in
  // let rows'=CR.extend1 vs rows in
  // let t   = SX.system_of_contract r g b in
  // let ios = inputs_with_oracles_contract_definition rows r g b in
  // let stp = SI.system_step_result t ios in

  // let iosr = inputs_with_oracles rows r in
  // let stpr = SI.system_step_result (SX.system_of_exp r) iosr in

  // let iosg = inputs_with_oracles rows' g in
  // let stpg = SI.system_step_result (SX.system_of_exp g) iosg in

  // let iosb = inputs_with_oracles rows b in
  // let stpb = SI.system_step_result (SX.system_of_exp b) iosb in

  // let o = SB.type_join_tup
  //   (SXP.step_oracle rows r)
  //   (SB.type_join_tup
  //     (SXP.step_oracle rows' g)
  //     (SXP.step_oracle rows b))
  // in
  // match rows with
  // | [row1] ->
  //   SXP.invariant_init r;
  //   SXP.invariant_init g;
  //   SXP.invariant_init b;

  //   SXP.invariant_step [] row1  r (SX.system_of_exp r).init;
  //   SXP.invariant_step [] (CR.cons stp.v row1) g (SX.system_of_exp g).init;
  //   SXP.invariant_step [] row1 b (SX.system_of_exp b).init;

  //   assert (vs == [stpb.v]);
  //   assert (rows' == [stpb.v, row1]);
  //   assert (stp == t.step (List.hd rows) o t.init);
  //   assert (stpr == (SX.system_of_exp r).step (List.hd rows) (SB.type_join_fst o) (SB.type_join_fst t.init));
  //   assert (stpb == (SX.system_of_exp b).step (List.hd rows) (SB.type_join_snd (SB.type_join_snd o)) (SB.type_join_snd (SB.type_join_snd t.init)));
  //   assert (stpg == (SX.system_of_exp g).step (stpb.v, List.hd rows) (SB.type_join_fst (SB.type_join_snd o)) (SB.type_join_fst (SB.type_join_snd t.init)));

  //   assert (SB.option_prop_sem stp.chck.assumptions <==> (
  //       b2t stpr.v /\
  //       SB.option_prop_sem stpr.chck.assumptions /\
  //       SB.option_prop_sem stpg.chck.assumptions /\
  //       SB.option_prop_sem stpb.chck.assumptions));
  //   assert (SB.option_prop_sem stp.chck.obligations <==> (
  //       b2t stpg.v /\
  //       SB.option_prop_sem stpr.chck.obligations /\
  //       SB.option_prop_sem stpg.chck.obligations /\
  //       SB.option_prop_sem stpb.chck.obligations));
  //   ()
  // | hd :: tl ->
  //   let hd' = List.hd rows' in
  //   let tl' = List.tl rows' in
  //   contract_invariant_holds tl r g b;

  //   let stp0  = SI.system_step_result t (inputs_with_oracles_contract_definition tl r g b) in

  //   SXP.invariant_step tl hd r (SB.type_join_fst stp0.s);
  //   SXP.invariant_step tl' hd' g (SB.type_join_fst (SB.type_join_snd stp0.s));
  //   SXP.invariant_step tl hd b (SB.type_join_snd (SB.type_join_snd stp0.s));

  //   assert (stp == t.step hd o stp0.s);
  //   assert (stpr == (SX.system_of_exp r).step hd (SB.type_join_fst o) (SB.type_join_fst stp0.s));
  //   assert (stpb == (SX.system_of_exp b).step hd (SB.type_join_snd (SB.type_join_snd o)) (SB.type_join_snd (SB.type_join_snd stp0.s)));
  //   assert (stpg == (SX.system_of_exp g).step (stpb.v, hd) (SB.type_join_fst (SB.type_join_snd o)) (SB.type_join_fst (SB.type_join_snd stp0.s)));

  //   assert (SB.option_prop_sem stp.chck.assumptions <==> (
  //       b2t stpr.v /\
  //       SB.option_prop_sem stpr.chck.assumptions /\
  //       SB.option_prop_sem stpg.chck.assumptions /\
  //       SB.option_prop_sem stpb.chck.assumptions));
  //   assert (SB.option_prop_sem stp.chck.obligations <==> (
  //       b2t stpg.v /\
  //       SB.option_prop_sem stpr.chck.obligations /\
  //       SB.option_prop_sem stpg.chck.obligations /\
  //       SB.option_prop_sem stpb.chck.obligations));
  //   ()
  (* TODO:ADMIT:update to latest F* 20251116 *)
  admit ()



let rec system_holds_exp_of_contract
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
      XB.bigstep_always rows r /\
      SI.system_holds_all (SX.system_of_contract r g b)
    ))
    (ensures (
      let vs  = XC.lemma_bigsteps_total_vs rows b in
      let rows'=CR.extend1 vs rows in
      let ios = inputs_with_oracles_contract_definition rows r g b in
      let stp = SI.system_step_result (SX.system_of_contract r g b) ios in

      SI.system_assumptions_sofar (SX.system_of_contract r g b) (inputs_with_oracles_contract_definition rows r g b) /\

      check_invariant PM.check_mode_unknown rows r /\
      check_invariant PM.check_mode_unknown rows' g /\
      check_invariant PM.check_mode_unknown rows b /\
      XB.bigstep_always rows' g
    ))
  =
  // let vs  = XC.lemma_bigsteps_total_vs rows b in
  // let rows'=CR.extend1 vs rows in
  // let t   = SX.system_of_contract r g b in
  // let ios = inputs_with_oracles_contract_definition rows r g b in
  // let stp = SI.system_step_result t ios in

  // let iosr = inputs_with_oracles rows r in
  // let stpr = SI.system_step_result (SX.system_of_exp r) iosr in

  // let iosg = inputs_with_oracles rows' g in
  // let stpg = SI.system_step_result (SX.system_of_exp g) iosg in

  // let iosb = inputs_with_oracles rows b in
  // let stpb = SI.system_step_result (SX.system_of_exp b) iosb in

  // let o = SB.type_join_tup
  //   (SXP.step_oracle rows r)
  //   (SB.type_join_tup
  //     (SXP.step_oracle rows' g)
  //     (SXP.step_oracle rows b))
  // in
  // SXCI.check_invariant_of_check_base PM.check_mode_valid rows r;
  // SXCI.check_invariant_of_check_base PM.check_mode_valid rows' g;
  // SXCI.check_invariant_of_check_base PM.check_mode_valid rows b;
  // contract_invariant_holds rows r g b;
  // match rows with
  // | [hd] ->
  //   check_init PM.check_mode_unknown r;
  //   check_init PM.check_mode_unknown g;
  //   check_init PM.check_mode_unknown b;

  //   SXP.invariant_init r;
  //   SXP.invariant_init g;
  //   SXP.invariant_init b;

  //   let hd' = List.hd rows' in
  //   assert (rows' == [hd']);
  //   assert (check_invariant PM.check_mode_valid [hd'] g);
  //   assert (check_invariant PM.check_mode_unknown [] g);

  //   SXCA.check_step_asm [] hd r (SB.type_join_fst t.init);
  //   SXCA.check_step_asm [] hd' g (SB.type_join_fst (SB.type_join_snd t.init));
  //   SXCA.check_step_asm [] hd b (SB.type_join_snd (SB.type_join_snd t.init));

  //   SXCO.check_step_obl [] hd r (SB.type_join_fst t.init);
  //   SXCO.check_step_obl [] hd' g (SB.type_join_fst (SB.type_join_snd t.init));
  //   SXCO.check_step_obl [] hd b (SB.type_join_snd (SB.type_join_snd t.init));
  //   ()

  // | hd :: tl ->
  //   let hd' = List.hd rows' in
  //   let tl' = List.tl rows' in
  //   let ios = inputs_with_oracles_contract_definition tl r g b in
  //   let stp0 = SI.system_step_result (SX.system_of_contract r g b) ios in

  //   contract_invariant_holds tl r g b;
  //   system_holds_exp_of_contract tl r g b;

  //   SXCA.check_step_asm tl hd r (SB.type_join_fst stp0.s);
  //   SXCA.check_step_asm tl' hd' g (SB.type_join_fst (SB.type_join_snd stp0.s));
  //   SXCA.check_step_asm tl hd b (SB.type_join_snd (SB.type_join_snd stp0.s));

  //   SXCO.check_step_obl tl hd r (SB.type_join_fst stp0.s);
  //   SXCO.check_step_obl tl' hd' g (SB.type_join_fst (SB.type_join_snd stp0.s));
  //   SXCO.check_step_obl tl hd b (SB.type_join_snd (SB.type_join_snd stp0.s));
  //   ()
  (* TODO:ADMIT:update to latest F* 20251116 *)
  admit ()
