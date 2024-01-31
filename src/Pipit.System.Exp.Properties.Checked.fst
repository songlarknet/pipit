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
module XK = Pipit.Exp.Checked.Base

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


// let eval_step'
//     (#t: table) (#c: context t) (#a: t.ty)
//     (rows: list (row c))
//     (row1: row c)
//     (e: exp t c a { XC.causal e })
//     (s: SB.option_type_sem (SX.state_of_exp e) { SXP.system_of_exp_invariant rows e s })
//     : Tot (orcl: SB.option_type_sem (SX.oracle_of_exp e) {
//         let stp = (SX.system_of_exp e).step row1 orcl s in
//         stp.v == XC.lemma_bigstep_total_v (row1::rows) e /\ SXP.system_of_exp_invariant (row1 :: rows) e stp.s
//       }) =
//   let (| v, hBS |) = XC.lemma_bigstep_total (row1 :: rows) e in
//   SXP.step_invariant_step rows row1 e v hBS s


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
  // match ps with
  // | PM.PSUnknown ->
  //   ()
  // | PM.PSValid ->
    ()



let rec check_step_asm
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (row1: row c)
    (e: exp t c a { XC.causal e })
    (v: t.ty_sem a)
    (hBS: XB.bigstep (row1 :: rows) e v)
    (s: SB.option_type_sem (SX.state_of_exp e) { SXP.system_of_exp_invariant rows e s })
    : Lemma (requires (
        check_invariant (row1 :: rows) e PM.check_mode_valid /\
        check_invariant          rows  e PM.check_mode_unknown))
      (ensures (
        let orcl = SXP.step_invariant_step rows row1 e v hBS s in
        let stp = (SX.system_of_exp e).step row1 orcl s in
        SB.option_prop_sem stp.chck.assumptions))
      (decreases e) =
    let orcl = SXP.step_invariant_step rows row1 e v hBS s in
    let stp = (SX.system_of_exp e).step row1 orcl s in
    match e with
    // | XBase b -> ()
    // | XApps _ -> admit ()
    // | XFby v1 e2 ->
    //   let (| v2, hBS2 |) = XC.lemma_bigstep_total (row1 :: rows) e2 in
    //   let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
    //   check_step_asm rows row1 e2 v2 hBS2 (SB.type_join_snd s)

    // | XMu e1 ->
    //   let (| vs', hBSMus'|) = XC.lemma_bigsteps_total (row1 :: rows) (XMu e1) in
    //   let XB.BSsS _ _ vs _ _ hBSMus hBSMu = hBSMus' in
    //   XB.bigstep_deterministic hBS hBSMu;
    //   let rows' = CR.zip2_cons vs rows in
    //   let row1' = CR.cons v row1 in
    //   let hBS1: XB.bigstep (row1' :: rows') e1 v = XC.lemma_bigstep_substitute_elim_XMu (row1 :: rows) e1 (v :: vs) hBSMus' in
    //   check_step_asm rows' row1' e1 v hBS1 s;
    //   ()

    // | XLet b e1 e2 ->
    //   let (| vlefts', hBS1s' |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
    //   let XB.BSsS _ _ vlefts _ vleft hBS1s hBS1 = hBS1s' in
    //   let rows' = CR.zip2_cons vlefts rows in
    //   let row1' = CR.cons vleft row1 in
    //   let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    //   let hBS2 = XC.lemma_bigstep_substitute_elim_XLet (row1 :: rows) e1 vlefts' hBS1s' e2 v hBS in
    //   assert (check_invariant (row1 :: rows) e1 PM.check_mode_valid);
    //   assert (check_invariant (row1' :: rows') e2 PM.check_mode_valid);
    //   check_step_asm rows row1 e1 vleft hBS1 (SB.type_join_fst s);
    //   check_step_asm rows' row1' e2 v hBS2 (SB.type_join_snd s);
    //   ()

    // | XCheck ps e1 ->
    //   // normalize_term_spec (check_invariant (row1 :: rows) (XCheck ps e1) PM.check_mode_valid);
    //   // norm_spec [delta; zeta; nbe; iota; primops] (check_invariant (row1 :: rows) (XCheck ps e1) PM.check_mode_valid);
    //   assert (check_invariant (row1 :: rows) e1 PM.check_mode_valid);
    //   assert (PM.prop_status_contains PM.check_mode_valid ps ==> XB.bigstep_always (row1 :: rows) e1);
    //   check_step_asm rows row1 e1 s;

    //   let orcl1 = eval_step' rows row1 e1 s in
    //   let stp1 = (SX.system_of_exp e1).step row1 orcl1 s in

    //   assert (XB.bigstep (row1 :: rows) e1 stp1.v);
    //   assert (XB.bigstep_always (row1 :: rows) e1 ==> XB.bigstep (row1 :: rows) e1 true);
    //   if PM.prop_status_contains PM.check_mode_valid ps then
    //   XB.bigstep_deterministic_squash (row1 :: rows) e1 stp1.v true
    //   else ();
    //   ()


    | XContract ps er eg eb ->
      let (| vs', hBSbs' |) = XC.lemma_bigsteps_total (row1 :: rows) eb in
      let XB.BSsS _ _ vs _ _ hBSbs hBSb = hBSbs' in
      let XB.BSContract _ _ _ _ _ _ hBSb' = hBS in
      XB.bigstep_deterministic hBSb hBSb';
      let rows' = CR.zip2_cons vs rows in
      let row1' = CR.cons v row1 in
      let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in

      let (| vr, hBSr |) = XC.lemma_bigstep_total (row1 :: rows)  er in
      let (| vg, hBSg |) = XC.lemma_bigstep_total (row1' :: rows') eg in

      assert (check_invariant (row1 :: rows) er PM.check_mode_valid);
      assert (check_invariant (row1' :: rows') eg PM.check_mode_valid);
      check_step_asm rows row1  er vr hBSr (SB.type_join_fst s);
      check_step_asm rows' row1' eg vg hBSg (SB.type_join_snd s);

      // assert (XB.bigstep (row1 :: rows) er stp1.v);
      assert (XB.bigstep_always (row1 :: rows) er ==> XB.bigstep (row1 :: rows) er true);
      assert (PM.prop_status_contains PM.check_mode_valid PM.PSValid ==> (XB.bigstep_always (row1 :: rows) er ==> XB.bigstep_always (row1' :: rows') eg));

      introduce PM.prop_status_contains PM.check_mode_valid ps ==> b2t vr
      with pm.
        XB.bigstep_deterministic_squash (row1 :: rows) er vr true;

      introduce b2t vr ==> b2t vg
      with hVr. (
        XB.bigstep_deterministic_squash (row1 :: rows) er vr true;
        assert (XB.bigstep (row1 :: rows) er true);

        (match ps with
        | PM.PSValid -> assert (XB.bigstep_always (row1 :: rows) er)
        | PM.PSUnknown -> assert (XB.bigstep_always rows er));
        assert (XB.bigstep_always rows er);
        assert (XB.bigstep_always (row1 :: rows) er)
        // XB.bigstep_deterministic_squash (row1' :: rows') eg vg true
      );


      // assume (b2t vr ==> b2t vg);
      // assume (PM.prop_status_contains PM.check_mode_valid ps ==> b2t vr);
      admit ()

    | _ -> admit ()

//     | XApps e1 ->
//       let XB.BSApps _ _ _ hBSa = hBS in
//       let orcl = check_apps_invariant_step rows row1 e1 v hBSa SX.system_of_exp_apps_const () s in
//       orcl

//     | XFby v1 e2 ->
//       let (| v2, hBS2 |) = XC.lemma_bigstep_total (row1 :: rows) e2 in
//       let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
//       let orcl = check_invariant_step rows row1 e2 v2 hBS2 (SB.type_join_snd s) in
//       (match hBS with
//       | XB.BSFby1 _ _ _ ->
//         orcl
//       | XB.BSFbyS _ _ _ _ _ hBS' ->
//       //XXX don't need squash
//         XB.bigstep_deterministic_squash rows e2 v (SB.type_join_fst s);
//         orcl)

//     | XMu e1 ->
//       let (| vs', hBSMus'|) = XC.lemma_bigsteps_total (row1 :: rows) (XMu e1) in
//       let XB.BSsS _ _ vs _ v' hBSMus hBSMu = hBSMus' in
//       XB.bigstep_deterministic hBS hBSMu;
//       assert (vs' == v :: vs);
//       let rows' = CR.zip2_cons vs rows in
//       let row1' = CR.cons v row1 in
//       let s: SB.option_type_sem (SX.state_of_exp e1) = s in
//       assert (system_of_exp_invariant rows' e1 s);

//       let hBS1: XB.bigstep (row1' :: rows') e1 v = XC.lemma_bigstep_substitute_elim_XMu (row1 :: rows) e1 (v :: vs) hBSMus' in

//       let orcl1 = check_invariant_step rows' row1' e1 v hBS1 s in
//       let orcl: SB.option_type_sem (SX.oracle_of_exp (XMu e1)) = SB.type_join_tup #(Some (t.ty_sem a)) #(SX.oracle_of_exp e1) v orcl1 in

//       let stp = (SX.system_of_exp (XMu e1)).step row1 orcl s in
//       assert (system_of_exp_invariant (row1 :: rows) (XMu e1) stp.s);
//       orcl

//     | XLet b e1 e2 ->
//       let (| vlefts', hBS1s' |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
//       let XB.BSsS _ _ vlefts _ vleft hBS1s hBS1 = hBS1s' in
//       let rows' = CR.zip2_cons vlefts rows in
//       let row1' = CR.cons vleft row1 in
//       let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
//       assert (system_of_exp_invariant rows  e1 (SB.type_join_fst s));
//       assert (system_of_exp_invariant rows' e2 (SB.type_join_snd s));

//       let hBS2 = XC.lemma_bigstep_substitute_elim_XLet (row1 :: rows) e1 vlefts' hBS1s' e2 v hBS in

//       let orcl1 = check_invariant_step rows  row1  e1 vleft hBS1 (SB.type_join_fst s) in
//       let orcl2 = check_invariant_step rows' row1' e2 v     hBS2 (SB.type_join_snd s) in
//       let orcl  = SB.type_join_tup orcl1 orcl2 in
//       orcl

//     | XCheck _ e1 ->
//       let XB.BSCheck _ _ _ v1 hBS1 = hBS in
//       check_invariant_step rows row1 e1 v1 hBS1 s

//     | XContract ps er eg eb ->
//       let (| vs', hBSbs' |) = XC.lemma_bigsteps_total (row1 :: rows) eb in
//       let XB.BSsS _ _ vs _ _ hBSbs hBSb = hBSbs' in
//       let XB.BSContract _ _ _ _ _ _ hBSb' = hBS in
//       XB.bigstep_deterministic hBSb hBSb';
//       let rows' = CR.zip2_cons vs rows in
//       let row1' = CR.cons v row1 in
//       let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in

//       let (| vr, hBSr |) = XC.lemma_bigstep_total (row1 :: rows)  er in
//       let (| vg, hBSg |) = XC.lemma_bigstep_total (row1' :: rows') eg in

//       let or = check_invariant_step rows row1  er vr hBSr (SB.type_join_fst s) in
//       let og = check_invariant_step rows' row1' eg vg hBSg (SB.type_join_snd s) in
//       let orcl = SB.type_join_tup #(Some (t.ty_sem a)) v (SB.type_join_tup or og) in

//       orcl

// and check_apps_invariant_step
//     (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
//     (rows: list (row c))
//     (row1: row c)
//     (e: exp_apps t c a { XC.causal_apps e })
//     (v: funty_sem t.ty_sem a)
//     (hBS: XB.bigstep_apps (row1 :: rows) e v)
//     (f: funty_sem t.ty_sem a -> inp -> res)
//     (inp0: inp)
//     (s: SB.option_type_sem (SX.state_of_exp_apps e) { system_of_exp_apps_invariant rows e s })
//     : Tot (orcl: SB.option_type_sem (SX.oracle_of_exp_apps e) {
//         let stp = (SX.system_of_exp_apps e f).step (inp0, row1) orcl s in
//         stp.v == f v inp0 /\
//         system_of_exp_apps_invariant (row1 :: rows) e stp.s
//       })
//       (decreases e) =
//   match e with
//   | XPrim _ -> ()
//   | XApp e1 e2 ->
//     let XB.BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
//     let f' = SX.system_of_exp_apps_distr f in
//     let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in
//     let orcl2 = check_invariant_step      rows row1 e2 v2 hBS2 (SB.type_join_fst s) in
//     let orcl1 = check_apps_invariant_step rows row1 e1 v1 hBS1 f' (v2, inp0) (SB.type_join_snd s) in
//     let orcl = SB.type_join_tup orcl2 orcl1 in
//     orcl


// let rec system_invariant_many
//     (#t: table) (#c: context t) (#a: t.ty)
//     (inputs: list (row c))
//     (e: exp t c a { XC.causal e })
//     : Tot (
//         state:   SB.option_type_sem (SX.state_of_exp e) { system_of_exp_invariant inputs e state } &
//         oracles: list (SB.option_type_sem (SX.oracle_of_exp e)) { List.length oracles == List.length inputs } &
//         results: list (t.ty_sem a) { List.length results == List.length inputs } &
//         XB.bigsteps inputs e results &
//         squash (
//           SB.system_steps (SX.system_of_exp e) inputs oracles == (state, results)
//         )) =
//     let t = SX.system_of_exp e in
//     match inputs with
//     | [] ->
//       check_init e;
//       assert (SB.system_steps (SX.system_of_exp e) inputs [] == (t.init, []));
//       (| t.init, [], [], XB.BSs0 e, () |)
//     | i :: inputs' ->
//       let (| s, oracles, results, hBSs, prf |) = system_invariant_many inputs' e in
//       let (| r, hBS |) = XC.lemma_bigstep_total (i :: inputs') e in
//       let o = step_invariant_step inputs' i e r hBS s in
//       let stp = t.step i o s in
//       assert (SB.system_steps (SX.system_of_exp e)       inputs'        oracles  == (    s,      results));
//       assert (SB.system_steps (SX.system_of_exp e) (i :: inputs') (o :: oracles) == (stp.s, r :: results));
//       assert (SB.system_steps (SX.system_of_exp e)       inputs   (o :: oracles) == (stp.s, r :: results));
//       let hBSs': XB.bigsteps (i :: inputs') e (r :: results) = XB.BSsS _ e _ _ _ hBSs hBS in
//       (| stp.s, o :: oracles, r :: results, hBSs', () |)


// (* Section 4, Theorem 4, translation-abstraction *)
// let system_translation_abstraction
//     (#t: table) (#c: context t) (#a: t.ty)
//     (inputs: list (row c))
//     (e: exp t c a { XC.causal e })
//     (results: list (t.ty_sem a) { List.length results == List.length inputs })
//     (hBSs: XB.bigsteps inputs e results)
//     : Tot (oracles: list (SB.option_type_sem (SX.oracle_of_exp e)) {
//           List.length oracles == List.length inputs /\
//           snd (SB.system_steps (SX.system_of_exp e) inputs oracles) == results
//       }) =
//   let (| s, oracles, results', hBSs', prf |) = system_invariant_many inputs e in
//   XB.bigsteps_proof_equivalence hBSs hBSs';
//   oracles
