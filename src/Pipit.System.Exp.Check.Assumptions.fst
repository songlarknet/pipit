module Pipit.System.Exp.Check.Assumptions

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality

module PM  = Pipit.Prop.Metadata

module T   = FStar.Tactics

#push-options "--split_queries always"

let step_XContract_asm' (#t: table) (#c: context t) (#a: t.ty)
  (ps: PM.prop_status)
  (er: exp t c t.propty { XC.causal er })
  (eg: exp t (a::c) t.propty { XC.causal eg })
  (eb: exp t c a { XC.causal eb })
  (rows: list (row c))
  (row1: row c)
  (s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) { SXP.system_of_exp_invariant rows (XContract ps er eg eb) s })
  : Lemma
    (requires (
      let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) eb in

      let rows' = CR.extend1 vs rows in
      let row1' = CR.cons v row1 in

      let stpr = eval_step rows row1 er (SB.type_join_fst s) in
      let stpg = eval_step rows' row1' eg (SB.type_join_snd s) in
    (SB.option_prop_sem stpr.chck.assumptions /\
      (b2t stpr.v ==> SB.option_prop_sem stpg.chck.assumptions) /\
      (b2t stpr.v ==> b2t stpg.v) /\
      (ps == PM.PSValid ==> b2t stpr.v))
  ))
    (ensures (
    let stp = eval_step rows row1 (XContract ps er eg eb) s in
    SB.option_prop_sem stp.chck.assumptions
  ))
  = ()

let contract_always_rely
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (row1: row c)
    (ps: PM.contract_status)
    (er: exp t       c  t.propty { XC.causal er })
    (eg: exp t (a :: c) t.propty { XC.causal eg })
    (eb: exp t       c         a { XC.causal eb })
    : Lemma (requires (
        check_invariant PM.check_mode_valid  (row1 :: rows) (XContract ps er eg eb) /\
        check_invariant PM.check_mode_unknown         rows  (XContract ps er eg eb)))
      (ensures (
        XB.bigstep_always rows er))
        =
    ()



let rec check_step_asm
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (row1: row c)
  (e: exp t c a { XC.causal e })
  (s: SB.option_type_sem (SX.state_of_exp e) { SXP.system_of_exp_invariant rows e s })
  : Lemma (requires (
      check_invariant PM.check_mode_valid  (row1 :: rows) e /\
      check_invariant PM.check_mode_unknown         rows  e))
    (ensures (
      let stp = eval_step rows row1 e s in
      SB.option_prop_sem stp.chck.assumptions))
    (decreases e) =
  match e with
  | XBase b -> ()

  | XApps e1 ->
    check_step_apps_asm rows row1 e1 SX.system_of_exp_apps_const () s

  | XFby v1 e2 ->
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
    check_step_asm rows row1 e2 (SB.type_join_snd s)

  | XMu e1 ->
    let (| v :: vs, hBSs |) = XC.lemma_bigsteps_total (row1 :: rows) (XMu e1) in
    let rows' = CR.extend1 vs rows in
    let row1' = CR.cons v row1 in
    check_step_asm rows' row1' e1 s;
    let hBS1 = XC.lemma_bigstep_substitute_elim_XMu (row1 :: rows) e1 (v :: vs) hBSs in
    XB.bigstep_deterministic_squash (row1' :: rows') e1 v (XC.lemma_bigstep_total_v (row1' :: rows') e1);
    ()

  | XLet b e1 e2 ->
    let (| vleft :: vlefts, hBS1s |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
    let rows' = CR.extend1 vlefts rows in
    let row1' = CR.cons vleft row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    check_step_asm rows row1 e1 (SB.type_join_fst s);
    check_step_asm rows' row1' e2 (SB.type_join_snd s);
    ()

  | XCheck ps e1 ->
    assert (check_invariant PM.check_mode_valid (row1 :: rows) e1);
    assert (PM.prop_status_contains PM.check_mode_valid ps ==> XB.bigstep_always (row1 :: rows) e1);
    check_step_asm rows row1 e1 s;
    let stp1 = eval_step rows row1 e1 s in
    introduce PM.prop_status_contains PM.check_mode_valid ps ==> b2t stp1.v
    with pm. (
      assert (XB.bigstep_always (row1 :: rows) e1);
      assert (b2t stp1.v)
    );
    ()

  | XContract ps er eg eb ->
    contract_always_rely rows row1 ps er eg eb;
    let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) eb in
    let rows' = CR.extend1 vs rows in
    let row1' = CR.cons v row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in

    let stpr = eval_step rows row1 er (SB.type_join_fst s) in
    let stpg = eval_step rows' row1' eg (SB.type_join_snd s) in
    let vr = stpr.v in
    let vg = stpg.v in

    check_step_asm rows row1  er (SB.type_join_fst s);
    introduce b2t vr ==> SB.option_prop_sem stpg.chck.assumptions
    with hvr.
      check_step_asm rows' row1' eg (SB.type_join_snd s);

    assert (vr == XC.lemma_bigstep_total_v (row1  :: rows)  er);
    assert (vg == XC.lemma_bigstep_total_v (row1' :: rows') eg);
    assert (XB.bigstep_always rows er);
    introduce PM.prop_status_contains PM.check_mode_valid ps ==> b2t vr
    with pm. (
      assert (XB.bigstep_always (row1 :: rows) er);
      assert (b2t vr)
    );
    introduce b2t vr ==> b2t vg
    with hVr. (
      assert (XB.bigstep_always rows er);
      assert (XB.bigstep (row1 :: rows) er vr);
      assert (XB.bigstep_always (row1 :: rows) er);
      assert (XB.bigstep_always (row1' :: rows') eg);
      assert (XC.lemma_bigstep_total_v (row1' :: rows') eg == vg);
      assert (vg == true)
    );
    step_XContract_asm' ps er eg eb rows row1 s;
    ()

and check_step_apps_asm
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (rows: list (row c))
  (row1: row c)
  (e: exp_apps t c a { XC.causal_apps e })
  (f: funty_sem t.ty_sem a -> inp -> res)
  (inp0: inp)
  (s: SB.option_type_sem (SX.state_of_exp_apps e) { SXP.system_of_exp_apps_invariant rows e s })
  : Lemma (requires (
      check_apps_invariant PM.check_mode_valid   (row1 :: rows) e /\
      check_apps_invariant PM.check_mode_unknown          rows  e))
    (ensures (
      let stp = eval_step_apps rows row1 e f inp0 s in
      SB.option_prop_sem stp.chck.assumptions))
    (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let v2 = XC.lemma_bigstep_total_v (row1 :: rows) e2 in
    let f' = SX.system_of_exp_apps_distr f in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in
    check_step_asm rows row1 e2 (SB.type_join_fst s);
    check_step_apps_asm rows row1 e1 f' (v2, inp0) (SB.type_join_snd s);
    ()
