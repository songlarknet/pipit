module Pipit.System.Exp.Check.Obligations

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

module CR = Pipit.Context.Row

module SB = Pipit.System.Base
module SX = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties

module XB = Pipit.Exp.Bigstep
module XC = Pipit.Exp.Causality

module PM = Pipit.Prop.Metadata

module T    = FStar.Tactics

#push-options "--split_queries always"


let step_XLet_obl' (#t: table) (#c: context t) (#a b: t.ty)
  (e1: exp t c b { XC.causal e1 })
  (e2: exp t (b::c) a { XC.causal e2 })
  (rows: list (row c))
  (row1: row c)
  (s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) { SXP.system_of_exp_invariant rows (XLet b e1 e2) s })
  : Lemma
    (requires (
      let stp = eval_step rows row1 (XLet b e1 e2) s in

      SB.option_prop_sem stp.chck.assumptions /\
      SB.option_prop_sem stp.chck.obligations
  ))
    (ensures (
      let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) e1 in

      let rows' = CR.zip2_cons vs rows in
      let row1' = CR.cons v row1 in
      let stp1 = eval_step rows row1 e1 (SB.type_join_fst s) in
      let stp2 = eval_step rows' row1' e2 (SB.type_join_snd s) in
      SB.option_prop_sem stp1.chck.assumptions /\
      SB.option_prop_sem stp2.chck.assumptions /\
      SB.option_prop_sem stp1.chck.obligations /\
      SB.option_prop_sem stp2.chck.obligations
  ))
  =
    let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) e1 in

    let rows' = CR.zip2_cons vs rows in
    let row1' = CR.cons v row1 in
    let stp1 = eval_step rows row1 e1 (SB.type_join_fst s) in
    let stp2 = eval_step rows' row1' e2 (SB.type_join_snd s) in

    let stp = eval_step rows row1 (XLet b e1 e2) s in

    assert (stp.chck == stp1.chck `SB.checks_join` stp2.chck);
    ()


// let step_XApp_obl' (#t: table) (#c: context t) (#ft: funty t.ty) (#a: t.ty) (#res #inp: Type0)
//   (ef: exp_apps t c (FTFun a ft) { XC.causal_apps ef })
//   (ea: exp      t c a  { XC.causal      ea })
//   (rows: list (row c))
//   (row1: row c)
//   (f: funty_sem t.ty_sem ft -> inp -> res)
//   (inp0: inp)
//   (s: SB.option_type_sem (SB.type_join (SX.state_of_exp ea) (SX.state_of_exp_apps ef)) { SXP.system_of_exp_apps_invariant rows (XApp ef ea) s })
//   : Lemma
//     (requires (
//       let stp = eval_step_apps rows row1 (XApp ef ea) f inp0 s in

//       SB.option_prop_sem stp.chck.assumptions /\
//       SB.option_prop_sem stp.chck.obligations
//   ))
//     (ensures (
//       let f' = SX.system_of_exp_apps_distr f in
//       let stpa = eval_step rows row1 ea (SB.type_join_fst s) in
//       let stpf = eval_step_apps rows row1 ef f' (stpa.v, inp0) (SB.type_join_snd s) in
//       SB.option_prop_sem stpf.chck.assumptions /\
//       SB.option_prop_sem stpa.chck.assumptions /\
//       SB.option_prop_sem stpf.chck.obligations /\
//       SB.option_prop_sem stpa.chck.obligations
//   ))
//   = ()

let rec check_step_obl
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (row1: row c)
  (e: exp t c a { XC.causal e })
  (s: SB.option_type_sem (SX.state_of_exp e) { SXP.system_of_exp_invariant rows e s })
  : Lemma (requires (
      let stp = eval_step rows row1 e s in
      check_invariant (row1 :: rows) e PM.check_mode_valid /\
      check_invariant          rows  e PM.check_mode_unknown /\
      SB.option_prop_sem stp.chck.assumptions /\
      SB.option_prop_sem stp.chck.obligations))
    (ensures (
      check_invariant (row1 :: rows) e PM.check_mode_unknown))
    (decreases e) =
  match e with
  | XBase b -> ()

  | XApps e1 ->
    check_step_apps_obl rows row1 e1 SX.system_of_exp_apps_const () s

  | XFby v1 e2 ->
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
    check_step_obl rows row1 e2 (SB.type_join_snd s)

  | XMu e1 ->
    let (| v :: vs, hBSs |) = XC.lemma_bigsteps_total (row1 :: rows) (XMu e1) in
    let rows' = CR.zip2_cons vs rows in
    let row1' = CR.cons v row1 in
    check_step_obl rows' row1' e1 s;
    let hBS1 = XC.lemma_bigstep_substitute_elim_XMu (row1 :: rows) e1 (v :: vs) hBSs in
    XB.bigstep_deterministic_squash (row1' :: rows') e1 v (XC.lemma_bigstep_total_v (row1' :: rows') e1);
    ()

  | XLet b e1 e2 ->
    let (| vleft :: vlefts, hBS1s |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
    let rows' = CR.zip2_cons vlefts rows in
    let row1' = CR.cons vleft row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    check_step_obl rows row1 e1 (SB.type_join_fst s);

    assert (check_invariant (row1' :: rows') e2 PM.check_mode_valid);
    assert (check_invariant          rows'  e2 PM.check_mode_unknown);

  // todo assert stp.assumptions => stp2.assumptions
    step_XLet_obl' b e1 e2 rows row1 s;
    // let stp  = eval_step rows' row1' e2 (SB.type_join_snd s) in
    // let stp1 = eval_step rows' row1' e2 (SB.type_join_snd s) in
    // let stp2 = eval_step rows' row1' e2 (SB.type_join_snd s) in
    // assert (stp.chck == stp1.chck `SB.checks_join` stp2.chck);
    // assert (SB.option_prop_sem stp.chck.assumptions ==> SB.option_prop_sem stp2.chck.assumptions);
    // assert (SB.option_prop_sem stp.chck.obligations ==> SB.option_prop_sem stp2.chck.obligations);

    check_step_obl rows' row1' e2 (SB.type_join_snd s);
    ()

  | XCheck ps e1 ->
    assert (ps == PM.PSUnknown ==> XB.bigstep_always rows e1);
    check_step_obl rows row1 e1 s;
    let stp1 = eval_step rows row1 e1 s in
    ()

  | XContract ps er eg eb ->
    let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) eb in
    let rows' = CR.zip2_cons vs rows in
    let row1' = CR.cons v row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in
    check_step_obl rows row1  er (SB.type_join_fst s);
    check_step_obl rows' row1' eg (SB.type_join_snd s);
    let stpr = eval_step rows row1 er (SB.type_join_fst s) in
    let stpg = eval_step rows' row1' eg (SB.type_join_snd s) in
    let vr = stpr.v in
    let vg = stpg.v in
    assert (vr == XC.lemma_bigstep_total_v (row1  :: rows)  er);
    assert (vg == XC.lemma_bigstep_total_v (row1' :: rows') eg);
    assert (XB.bigstep_always rows er);
    ()

and check_step_apps_obl
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (rows: list (row c))
  (row1: row c)
  (e: exp_apps t c a { XC.causal_apps e })
  (f: funty_sem t.ty_sem a -> inp -> res)
  (inp0: inp)
  (s: SB.option_type_sem (SX.state_of_exp_apps e) { SXP.system_of_exp_apps_invariant rows e s })
  : Lemma (requires (
      let stp = eval_step_apps rows row1 e f inp0 s in
      check_apps_invariant (row1 :: rows) e PM.check_mode_valid /\
      check_apps_invariant          rows  e PM.check_mode_unknown /\
      SB.option_prop_sem stp.chck.assumptions /\
      SB.option_prop_sem stp.chck.obligations))
    (ensures (
      check_apps_invariant (row1 :: rows) e PM.check_mode_unknown))
    (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let f' = SX.system_of_exp_apps_distr f in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in
    // step_XApp_obl' e1 e2 rows row1 f inp0 s;
    check_step_obl rows row1 e2 (SB.type_join_fst s);

    // let stp  = eval_step_apps rows row1 e f inp0 s in
    let stp2 = eval_step      rows row1 e2 (SB.type_join_fst s) in
    // let stp1 = eval_step_apps rows row1 e1 f' (stp2.v, inp0) (SB.type_join_snd s) in

    // assert (stp.chck == (stp1.chck `SB.checks_join` stp2.chck));

    check_step_apps_obl rows row1 e1 f' (stp2.v, inp0) (SB.type_join_snd s);
    ()
