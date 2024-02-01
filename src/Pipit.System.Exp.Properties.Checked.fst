module Pipit.System.Exp.Properties.Checked

open Pipit.Prim.Table
open Pipit.Exp.Base

module Table = Pipit.Prim.Table

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

module SB = Pipit.System.Base
module SX = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties

module X  = Pipit.Exp
module XB = Pipit.Exp.Bigstep
module XC = Pipit.Exp.Causality
// module XK = Pipit.Exp.Checked.Base

module PM = Pipit.Prop.Metadata

module List = FStar.List.Tot

module T    = FStar.Tactics

#push-options "--split_queries always"


(*
   The invariant describes the transition system's state after it has been fed with all of `rows` as inputs.
*)
let rec check_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  (mode: PM.check_mode):
    Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> check_apps_invariant rows e1 mode

  | XFby v1 e2 ->
    check_invariant rows e2 mode

  | XMu e1 ->
    check_invariant (CR.zip2_cons (XC.lemma_bigsteps_total_vs rows e) rows) e1 mode

  | XLet b e1 e2 ->
    check_invariant rows e1 mode /\
    check_invariant (CR.zip2_cons (XC.lemma_bigsteps_total_vs rows e1) rows) e2 mode

  | XCheck ps e1 ->
    check_invariant rows e1 mode /\
    (PM.prop_status_contains mode ps ==> XB.bigstep_always rows e1)

  | XContract ps er eg eb ->
    let rows' = CR.zip2_cons (XC.lemma_bigsteps_total_vs rows eb) rows in
    check_invariant rows  er mode /\
    check_invariant rows' eg mode /\
    (PM.prop_status_contains mode PM.PSValid ==> XB.bigstep_always rows er ==> XB.bigstep_always rows' eg) /\
    (PM.prop_status_contains mode ps ==> XB.bigstep_always rows er)

and check_apps_invariant
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e })
  (mode: PM.check_mode):
    Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 ->
    check_apps_invariant rows e1 mode /\
    check_invariant rows e2 mode

let rec check_init
    (#t: table) (#c: context t) (#a: t.ty)
    (e: exp t c a { XC.causal e })
    (mode: PM.check_mode)
    : Lemma (ensures check_invariant [] e mode)
      (decreases e) =
    let tx = SX.system_of_exp e in
    let rows: list (row c) = [] in
    match e with
    | XBase _ -> ()

    | XApps e1 ->
      check_apps_init e1 (fun r () -> r) mode;
      ()

    | XFby v1 e2 ->
      check_init e2 mode

    | XMu e1 ->
      check_init e1 mode;
      ()

    | XLet b e1 e2 ->
      check_init e1 mode;
      check_init e2 mode;
      ()

    | XCheck _ e1 ->
      check_init e1 mode

    | XContract ps er eg eb ->
      check_init er mode;
      check_init eg mode;
      ()

and check_apps_init
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    (mode: PM.check_mode)
    : Lemma (ensures
        check_apps_invariant [] e mode)
      (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let f' = SX.system_of_exp_apps_distr f in
    check_apps_init e1 f' mode;
    check_init e2 mode;
    ()

let eval_step
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (row1: row c)
    (e: exp t c a { XC.causal e })
    (s: SB.option_type_sem (SX.state_of_exp e) { SXP.system_of_exp_invariant rows e s })
    : stp: SB.step_result (SX.state_of_exp e) (t.ty_sem a) {
      stp.v == (XC.lemma_bigstep_total_v (row1 :: rows) e) /\ SXP.system_of_exp_invariant (row1 :: rows) e stp.s
    } =
  let orcl = SXP.step_oracle (row1 :: rows) e in
  SXP.invariant_step rows row1 e s;
  (SX.system_of_exp e).step row1 orcl s


let eval_step_apps
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (rows: list (row c))
    (row1: row c)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    (inp0: inp)
    (s: SB.option_type_sem (SX.state_of_exp_apps e) { SXP.system_of_exp_apps_invariant rows e s })
    : stp: SB.step_result (SX.state_of_exp_apps e) res {
      stp.v == f (dfst (XC.lemma_bigstep_apps_total (row1 :: rows) e)) inp0 /\
      SXP.system_of_exp_apps_invariant (row1 :: rows) e stp.s
    } =
  let orcl = SXP.step_apps_oracle (row1 :: rows) e in
  SXP.invariant_step_apps rows row1 e f inp0 s;
  (SX.system_of_exp_apps e f).step (inp0, row1) orcl s

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

      let rows' = CR.zip2_cons vs rows in
      let row1' = CR.cons v row1 in

      let stpr = eval_step rows row1 er (SB.type_join_fst s) in
      let stpg = eval_step rows' row1' eg (SB.type_join_snd s) in
    (SB.option_prop_sem stpr.chck.assumptions /\
      SB.option_prop_sem stpg.chck.assumptions /\
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
        check_invariant (row1 :: rows) (XContract ps er eg eb) PM.check_mode_valid /\
        check_invariant          rows  (XContract ps er eg eb) PM.check_mode_unknown))
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
      check_invariant (row1 :: rows) e PM.check_mode_valid /\
      check_invariant          rows  e PM.check_mode_unknown))
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
    let rows' = CR.zip2_cons vs rows in
    let row1' = CR.cons v row1 in
    check_step_asm rows' row1' e1 s;
    let hBS1 = XC.lemma_bigstep_substitute_elim_XMu (row1 :: rows) e1 (v :: vs) hBSs in
    XB.bigstep_deterministic_squash (row1' :: rows') e1 v (XC.lemma_bigstep_total_v (row1' :: rows') e1);
    ()

  | XLet b e1 e2 ->
    let (| vleft :: vlefts, hBS1s |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
    let rows' = CR.zip2_cons vlefts rows in
    let row1' = CR.cons vleft row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    check_step_asm rows row1 e1 (SB.type_join_fst s);
    check_step_asm rows' row1' e2 (SB.type_join_snd s);
    ()

  | XCheck ps e1 ->
    assert (check_invariant (row1 :: rows) e1 PM.check_mode_valid);
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
    let rows' = CR.zip2_cons vs rows in
    let row1' = CR.cons v row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in
    check_step_asm rows row1  er (SB.type_join_fst s);
    check_step_asm rows' row1' eg (SB.type_join_snd s);
    let stpr = eval_step rows row1 er (SB.type_join_fst s) in
    let stpg = eval_step rows' row1' eg (SB.type_join_snd s) in
    let vr = stpr.v in
    let vg = stpg.v in
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
      check_apps_invariant (row1 :: rows) e PM.check_mode_valid /\
      check_apps_invariant          rows  e PM.check_mode_unknown))
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
    contract_always_rely rows row1 ps er eg eb;
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

  | _ -> admit ()

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
