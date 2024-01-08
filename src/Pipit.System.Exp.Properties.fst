(* Translation to transition system proof *)
module Pipit.System.Exp.Properties

open Pipit.Prim.Table
open Pipit.Exp.Base

module Table = Pipit.Prim.Table

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

module SB = Pipit.System.Base
module SX = Pipit.System.Exp

module X  = Pipit.Exp
module XB = Pipit.Exp.Bigstep
module XC = Pipit.Exp.Causality

module List = FStar.List.Tot

module T    = FStar.Tactics

#push-options "--split_queries always"

(*
   The invariant describes the transition system's state after it has been fed with all of `rows` as inputs.
*)
let rec system_of_exp_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a)
  (s: SB.option_type_sem (SX.state_of_exp e)):
    Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> system_of_exp_apps_invariant rows e1 s

  | XFby v1 e2 ->
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
    (match rows with
    | [] -> SB.type_join_fst s == v1
    | _ :: _ -> XB.bigstep rows e2 (SB.type_join_fst s)) /\ system_of_exp_invariant rows e2 (SB.type_join_snd s)

  | XMu e1 ->
    let s: SB.option_type_sem (SX.state_of_exp e1) = coerce_eq () s in
    // let (| vs, hBSmus |) = XC.lemma_bigsteps_total rows e in
    exists (vs: list (t.ty_sem a) { List.length vs == List.length rows }).
      let rows' = CR.zip2_cons vs rows in
      XB.bigsteps rows' e1 vs /\ system_of_exp_invariant rows' e1 s

  | XLet b e1 e2 ->
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    // let (| vlefts, hBSlefts |) = XC.lemma_bigsteps_total rows e1 in
    exists (vlefts: list (t.ty_sem b) { List.length vlefts == List.length rows }).
      let rows' = CR.zip2_cons vlefts rows in
      XB.bigsteps rows e1 vlefts /\ 
      system_of_exp_invariant rows e1 (SB.type_join_fst s) /\
      system_of_exp_invariant rows' e2 (SB.type_join_snd s)

  | XCheck _ e1 ->
    let s: SB.option_type_sem (SX.state_of_exp e1) = s in
    system_of_exp_invariant rows e1 s

  | XContract _ er eg eb ->
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in
    exists (vs: list (t.ty_sem a) { List.length vs == List.length rows }).
      let rows' = CR.zip2_cons vs rows in
      XB.bigsteps rows eb vs /\
      system_of_exp_invariant rows  er (SB.type_join_fst s) /\
      system_of_exp_invariant rows' eg (SB.type_join_snd s)

and system_of_exp_apps_invariant
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp_apps t c a)
  (s: SB.option_type_sem (SX.state_of_exp_apps e)):
    Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 ->
    assert_norm (SX.state_of_exp_apps (XApp e1 e2) == SB.type_join(SX.state_of_exp e2) (SX.state_of_exp_apps e1));
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in
    system_of_exp_apps_invariant rows e1 (SB.type_join_snd s) /\
    system_of_exp_invariant rows e2 (SB.type_join_fst s)


// let step_invariant
//     (#t: table) (#c: context t) (#a: t.ty)
//     (row_prefix: list (row c))
//     (row1: row c)
//     (e: exp t c a)
//     (stp: SB.step_result (SX.state_of_exp e) (t.ty_sem a))
//       =
//   XB.bigstep (row1 :: row_prefix) e stp.v /\
//   system_of_exp_invariant (row1 :: row_prefix) e stp.s
// let step0_invariant
//     (#t: table) (#c: context t) (#a: t.ty)
//     (row1: row c)
//     (e: exp t c a)
//     (orcl: SB.option_type_sem (SX.oracle_of_exp e))
//       =
//   let t = SX.system_of_exp e in
//   let stp = t.step row1 orcl t.init in
//   step_invariant [] row1 e stp


// #push-options "--fuel 1 --ifuel 1"
let rec step0_ok
    (#t: table) (#c: context t) (#a: t.ty)
    (row1: row c)
    (e: exp t c a { XC.causal e })
    (v: t.ty_sem a)
    (hBS: XB.bigstep [row1] e v)
    : Tot (orcl: SB.option_type_sem (SX.oracle_of_exp e) {
        let stp = SB.system_step0 (SX.system_of_exp e) row1 orcl in
        stp.v == v /\ system_of_exp_invariant [row1] e stp.s
      } )
      (decreases e) =
    match e with
    | XBase _ -> ()

    | XApps e1 -> (match hBS with
      | XB.BSApps _ _ _ hBSa ->
        let t: SB.system (unit & row c) (SX.oracle_of_exp_apps e1) (SX.state_of_exp_apps e1) (t.ty_sem a) = SX.system_of_exp_apps e1 (fun r i -> r) in
        let t' = SB.system_with_input (fun s -> ((), s)) t in

        let orcl = step0_apps_ok row1 e1 v hBSa (fun r i -> r) () in

        let stp1 = t'.step row1 orcl t'.init in

        let tx   = SX.system_of_exp (XApps e1) in
        let stp =  tx.step row1 orcl tx.init in

        assert (stp1 == stp)
          by (T.norm [delta; nbe; zeta; iota; primops];
            T.dump "K");

        orcl)

    | XFby v1 e2 ->
      let (| v2, hBS2 |) = XC.lemma_bigstep_total [row1] e2 in
      step0_ok row1 e2 v2 hBS2

    | XMu e1 ->
      let vs = [v] in
      let rows' = CR.zip2_cons vs [row1] in
      let row1' = CR.cons v row1 in
      let hBSMus: XB.bigsteps [row1] e vs = XB.BSsS _ _ _ _ _ (XB.BSs0 e) hBS in
      let hBS1: XB.bigstep rows' e1 v = XC.lemma_bigstep_substitute_elim_XMu [row1] e1 vs hBSMus in
      let orcl1 = step0_ok row1' e1 v hBS1 in

      let orcl  = SB.type_join_tup #(Some (t.ty_sem a)) v orcl1 in

      let stp = SB.system_step0 (SX.system_of_exp e) row1 orcl in
      assert (stp.v == v);
      let hBSMus': XB.bigsteps rows' e1 vs = XB.BSsS _ _ _ row1' _ (XB.BSs0 e1) hBS1 in
      assert (system_of_exp_invariant [row1] e stp.s);
      orcl

    | XLet b e1 e2 ->
      let (| v1, hBS1 |) = XC.lemma_bigstep_total [row1] e1 in
      let hBS1s = XB.BSsS _ _ _ _ _ (XB.BSs0 e1) hBS1 in

      let vlefts = [v1] in
      let row1'  = CR.cons v1 row1 in
      let rows'  = CR.zip2_cons vlefts [row1] in

      let hBS2 = XC.lemma_bigstep_substitute_elim_XLet [row1] e1 vlefts hBS1s e2 v hBS in

      let orcl1 = step0_ok row1  e1 v1 hBS1 in
      let orcl2 = step0_ok row1' e2 v  hBS2 in
      let orcl  = SB.type_join_tup orcl1 orcl2 in
      orcl

    | XCheck _ e1 ->
      (match hBS with
      | XB.BSCheck _ _ _ v1 hBS1 ->
        step0_ok row1 e1 v1 hBS1)

    | XContract ps er eg eb ->
      let vs = [v] in
      let rows' = CR.zip2_cons vs [row1] in
      let row1' = CR.cons v row1 in
      let (| vr, hBSr |) = XC.lemma_bigstep_total [row1]  er in
      let (| vg, hBSg |) = XC.lemma_bigstep_total rows' eg in
      let hBSbs: XB.bigsteps [row1] eb [v] =
        match hBS with
        | XB.BSContract _ _ _ _ _ _ hBSb ->
          XB.BSsS _ _ _ _ _ (XB.BSs0 eb) hBSb in

      let or = step0_ok row1  er vr hBSr in
      let og = step0_ok row1' eg vg hBSg in
      let orcl = SB.type_join_tup #(Some (t.ty_sem a)) v (SB.type_join_tup or og) in

      let stp = SB.system_step0 (SX.system_of_exp e) row1 orcl in
      assert (stp.v == v);
      assert (system_of_exp_invariant [row1] e stp.s);
      orcl

and step0_apps_ok
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (row1: row c)
    (e: exp_apps t c a { XC.causal_apps e })
    (v: funty_sem t.ty_sem a)
    (hBS: XB.bigstep_apps [row1] e v)
    (f: funty_sem t.ty_sem a -> inp -> res)
    (inp0: inp)
    : Tot (orcl: SB.option_type_sem (SX.oracle_of_exp_apps e) {
        let stp = SB.system_step0 (SX.system_of_exp_apps e f) (inp0, row1) orcl in
        stp.v == f v inp0 /\
        system_of_exp_apps_invariant [row1] e stp.s
      })
      (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let XB.BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
    let f' = (fun r i -> f (r (fst i)) (snd i)) in

    let orcl2 = step0_ok      row1 e2 v2 hBS2 in
    let orcl1 = step0_apps_ok row1 e1 v1 hBS1 f' (v2, inp0) in

    let orcl = SB.type_join_tup orcl2 orcl1 in

    let t1 = SX.system_of_exp_apps e1 f' in
    let t2 = SX.system_of_exp e2 in

    let t: SB.system (inp & row c) (SX.oracle_of_exp_apps e) (SX.state_of_exp_apps e) res =
      (SX.system_of_exp_apps (XApp e1 e2) f) in

    let t'  =
      SB.system_let (fun i v -> ((v, fst i), snd i)) (SB.system_with_input (snd #inp) t2) t1 in

    assert (t == t') by (
      FStar.Tactics.norm [delta_only [`%SX.system_of_exp_apps]; zeta; primops; iota; nbe ];
      FStar.Tactics.trefl ());

    let stp = t.step (inp0, row1) orcl t.init in
    let stp2 = t2.step row1 (SB.type_join_fst orcl) t2.init in
    let stp1 = t1.step ((stp2.v, inp0), row1) (SB.type_join_snd orcl) t1.init in

    assert (stp2.v == v2);
    assert (stp1.v == f (v1 v2) inp0);

    assert (system_of_exp_apps_invariant [row1] e1 stp1.s);
    assert (system_of_exp_invariant [row1] e2 stp2.s);

    let s': SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = stp.s in

    assert (stp1.s == SB.type_join_snd s');
    assert (stp2.s == SB.type_join_fst s');

    let s': SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = stp.s in
    assert (stp.v == f v inp0);
    assert (system_of_exp_apps_invariant [row1] e stp.s);
    orcl


let rec stepn_ok
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c) { Cons? rows })
    (row1: row c)
    (e: exp t c a { XC.causal e })
    (v: t.ty_sem a)
    (hBS: XB.bigstep (row1 :: rows) e v)
    (s: SB.option_type_sem (SX.state_of_exp e) { system_of_exp_invariant rows e s })
    : Tot (orcl: SB.option_type_sem (SX.oracle_of_exp e) {
        let stp = (SX.system_of_exp e).step row1 orcl s in
        stp.v == v /\ system_of_exp_invariant (row1 :: rows) e stp.s
      } )
      (decreases e) =
    match e with
    // | XBase _ -> ()

    // | XApps e1 -> (match hBS with
    //   | XB.BSApps _ _ _ hBSa ->
    //     let t: SB.system (unit & row c) (SX.oracle_of_exp_apps e1) (SX.state_of_exp_apps e1) (t.ty_sem a) = SX.system_of_exp_apps e1 (fun r i -> r) in
    //     let t' = SB.system_with_input (fun s -> ((), s)) t in

    //     let orcl = stepn_apps_ok rows row1 e1 v hBSa (fun r i -> r) () s in

    //     let stp1 = t'.step row1 orcl s in

    //     let tx   = SX.system_of_exp (XApps e1) in
    //     let stp =  tx.step row1 orcl s in

    //     assert (stp1 == stp)
    //       by (T.norm [delta; nbe; zeta; iota; primops];
    //         T.dump "K");

    //     orcl)

    | XFby v1 e2 ->
      let (| v2, hBS2 |) = XC.lemma_bigstep_total (row1 :: rows) e2 in
      let orcl = stepn_ok rows row1 e2 v2 hBS2 s in
      let stp = (SX.system_of_exp e).step row1 orcl s in
      // let stp = 
      assert (system_of_exp_invariant rows e stp.s);
      orcl

    // | XMu e1 ->
    //   let vs = [v] in
    //   let rows' = CR.zip2_cons vs [row1] in
    //   let row1' = CR.cons v row1 in
    //   let hBSMus: XB.bigsteps [row1] e vs = XB.BSsS _ _ _ _ _ (XB.BSs0 e) hBS in
    //   let hBS1: XB.bigstep rows' e1 v = XC.lemma_bigstep_substitute_elim_XMu [row1] e1 vs hBSMus in
    //   let orcl1 = step0_ok row1' e1 v hBS1 in

    //   let orcl  = SB.type_join_tup #(Some (t.ty_sem a)) v orcl1 in

    //   let stp = SB.system_step0 (SX.system_of_exp e) row1 orcl in
    //   assert (stp.v == v);
    //   let hBSMus': XB.bigsteps rows' e1 vs = XB.BSsS _ _ _ row1' _ (XB.BSs0 e1) hBS1 in
    //   assert (system_of_exp_invariant [row1] e stp.s);
    //   orcl

    // | XLet b e1 e2 ->
    //   let (| v1, hBS1 |) = XC.lemma_bigstep_total [row1] e1 in
    //   let hBS1s = XB.BSsS _ _ _ _ _ (XB.BSs0 e1) hBS1 in

    //   let vlefts = [v1] in
    //   let row1'  = CR.cons v1 row1 in
    //   let rows'  = CR.zip2_cons vlefts [row1] in

    //   let hBS2 = XC.lemma_bigstep_substitute_elim_XLet [row1] e1 vlefts hBS1s e2 v hBS in

    //   let orcl1 = step0_ok row1  e1 v1 hBS1 in
    //   let orcl2 = step0_ok row1' e2 v  hBS2 in
    //   let orcl  = SB.type_join_tup orcl1 orcl2 in
    //   orcl

    // | XCheck _ e1 ->
    //   (match hBS with
    //   | XB.BSCheck _ _ _ v1 hBS1 ->
    //     step0_ok row1 e1 v1 hBS1)

    // | XContract ps er eg eb ->
    //   let vs = [v] in
    //   let rows' = CR.zip2_cons vs [row1] in
    //   let row1' = CR.cons v row1 in
    //   let (| vr, hBSr |) = XC.lemma_bigstep_total [row1]  er in
    //   let (| vg, hBSg |) = XC.lemma_bigstep_total rows' eg in
    //   let hBSbs: XB.bigsteps [row1] eb [v] =
    //     match hBS with
    //     | XB.BSContract _ _ _ _ _ _ hBSb ->
    //       XB.BSsS _ _ _ _ _ (XB.BSs0 eb) hBSb in

    //   let or = step0_ok row1  er vr hBSr in
    //   let og = step0_ok row1' eg vg hBSg in
    //   let orcl = SB.type_join_tup #(Some (t.ty_sem a)) v (SB.type_join_tup or og) in

    //   let stp = SB.system_step0 (SX.system_of_exp e) row1 orcl in
    //   assert (stp.v == v);
    //   assert (system_of_exp_invariant [row1] e stp.s);
    //   orcl
  | _ -> admit ()

and stepn_apps_ok
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (rows: list (row c) { Cons? rows })
    (row1: row c)
    (e: exp_apps t c a { XC.causal_apps e })
    (v: funty_sem t.ty_sem a)
    (hBS: XB.bigstep_apps (row1 :: rows) e v)
    (f: funty_sem t.ty_sem a -> inp -> res)
    (inp0: inp)
    (s: SB.option_type_sem (SX.state_of_exp_apps e) { system_of_exp_apps_invariant rows e s })
    : Tot (orcl: SB.option_type_sem (SX.oracle_of_exp_apps e) {
        let stp = (SX.system_of_exp_apps e f).step (inp0, row1) orcl s in
        stp.v == f v inp0 /\
        system_of_exp_apps_invariant (row1 :: rows) e stp.s
      })
      (decreases e) =
  match e with
  | _ -> admit ()
  // | XPrim _ -> ()
  // | XApp e1 e2 ->
  //   let XB.BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
  //   let f' = (fun r i -> f (r (fst i)) (snd i)) in
  //   let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in

  //   let orcl2 = stepn_ok      rows row1 e2 v2 hBS2 (SB.type_join_fst s) in
  //   let orcl1 = stepn_apps_ok rows row1 e1 v1 hBS1 f' (v2, inp0) (SB.type_join_snd s) in

  //   let orcl = SB.type_join_tup orcl2 orcl1 in

  //   let t1 = SX.system_of_exp_apps e1 f' in
  //   let t2 = SX.system_of_exp e2 in

  //   let t: SB.system (inp & row c) (SX.oracle_of_exp_apps e) (SX.state_of_exp_apps e) res =
  //     (SX.system_of_exp_apps (XApp e1 e2) f) in

  //   let t'  =
  //     SB.system_let (fun i v -> ((v, fst i), snd i)) (SB.system_with_input (snd #inp) t2) t1 in

  //   assert (t == t') by (
  //     FStar.Tactics.norm [delta_only [`%SX.system_of_exp_apps]; zeta; primops; iota; nbe ];
  //     FStar.Tactics.trefl ());

  //   let stp = t.step (inp0, row1) orcl s in
  //   let stp2 = t2.step row1 (SB.type_join_fst orcl) (SB.type_join_fst s) in
  //   let stp1 = t1.step ((stp2.v, inp0), row1) (SB.type_join_snd orcl) (SB.type_join_snd s) in

  //   assert (stp2.v == v2);
  //   assert (stp1.v == f (v1 v2) inp0);

  //   assert (system_of_exp_apps_invariant (row1 :: rows) e1 stp1.s);
  //   assert (system_of_exp_invariant (row1 :: rows) e2 stp2.s);

  //   let s': SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = stp.s in

  //   assert (stp1.s == SB.type_join_snd s');
  //   assert (stp2.s == SB.type_join_fst s');

  //   let s': SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = stp.s in
  //   assert (stp.v == f v inp0);
  //   assert (system_of_exp_apps_invariant (row1 :: rows) e stp.s);
  //   orcl





(*
let rec dstepn_ok
    (#t: table) (#c: context t)
    (rows: list (row c) { Cons? rows })
    (row: row c)
    (e: exp t c 'a { causal e })
    (v: 'a)
    (hBS: bigstep (row :: rows) e v)
    (s: state_of_exp e { system_of_exp_invariant rows e s }):
      Lemma (ensures (
        let t = dsystem_of_exp e in
        let (s', v') = t.step row s in
        v == v' /\ system_of_exp_invariant (row :: rows) e s'))
          (decreases e) =
    match e with
    | XVal _ -> ()
    | XPrim _ -> ()
    | XBVar _ -> ()
    | XVar _ -> false_elim ()

    | XApp e1 e2 ->
      assert_norm (causal (XApp e1 e2) == (causal e1 && causal e2));
      assert_norm (state_of_exp (XApp e1 e2) == (state_of_exp e1 & state_of_exp e2));
      let s: state_of_exp e1 & state_of_exp e2 = s in
      let (s1, s2) = s in
      assert_norm (system_of_exp_invariant rows (XApp e1 e2) (s1, s2) ==> (system_of_exp_invariant rows e1 s1 /\ system_of_exp_invariant rows e2 s2));
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t  = dsystem_ap2 t1 t2 in
      assert_norm (dsystem_of_exp (XApp e1 e2) == t);
      let BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
      dstepn_ok rows row e1 v1 hBS1 s1;
      dstepn_ok rows row e2 v2 hBS2 s2;
      let (s', v') = t.step row s in
      assert_norm (system_of_exp_invariant (row :: rows) (XApp e1 e2) s');
      ()

    | XFby v1 e2 ->
      let s: state_of_exp e2 & 'a = s in
      let (s1, v_buf) = s in

      let t2 = dsystem_of_exp e2 in
      let t  = dsystem_pre v1 t2 in

      let (| v2, hBS2 |) = lemma_bigstep_total (row :: rows) e2 in
      dstepn_ok rows row e2 v2 hBS2 s1;

      let (s', v') = t.step row s in
      assert (system_of_exp_invariant (row :: rows) (XFby v1 e2) s');
      // assert (v' == v_buf);
      let (| v'', hBS' |) = lemma_bigstep_total (row :: rows) (XFby v1 e2) in
      // TODO: rephrase bigstep_deterministic as:
      // bigstep rows e v ==> v = lemma_bigstep_total_v rows e
      // not sure if statement is best, should it just use bigstep_total_v?
      bigstep_deterministic hBS hBS';
      ()

    | XThen e1 e2 ->
      let s: system_then_state (state_of_exp e1) (state_of_exp e2) = s in
      assert_norm (List.Tot.length (row :: rows) > 1);
      let (| v1, hBS1 |) = lemma_bigstep_total (row :: rows) e1 in
      let BSThenS _ _ _ _ hBS2 = hBS in
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t = dsystem_then t1 t2 in
      assert_norm (dsystem_of_exp (XThen e1 e2) == t);
      dstepn_ok rows row e1 v1 hBS1 s.s1;
      dstepn_ok rows row e2 v hBS2 s.s2;
      let (s', v') = t.step row s in
      assert (system_of_exp_invariant (row :: rows) (XThen e1 e2) s');
      assert (v' == v);
      ()

    | XMu e1 ->
      assert_norm (state_of_exp (XMu e1) == state_of_exp e1);
      let s: state_of_exp (XMu e1) = s in
      let s: state_of_exp e1 = coerce_eq () s in
      let bottom = t.val_default (XMu?.valty e) in
      let t1 = dsystem_of_exp e1 in
      let t' = dsystem_mu_causal bottom (fun i v -> (v, i)) t1 in

      let (s_scrap, v0) = t1.step (bottom, row) s in
      let (s1', v') = t1.step (v0, row) s in

      let (| vpres, hBSs|) = lemma_bigsteps_total rows (XMu e1) in
      let (| v0x, hBSX |) = lemma_bigstep_total (CR.zip2_cons (bottom :: vpres) (row :: rows)) e1 in
      let hBSMu: bigstep (row :: rows) (XMu e1) v0x = lemma_bigstep_substitute_intros_XMu rows e1 vpres row v0x bottom hBSs hBSX in
      let hBSMus: bigsteps (row :: rows) (XMu e1) (v0x :: vpres) = BSsS _ _ _ _ _ hBSs hBSMu in

      dstepn_ok (CR.zip2_cons vpres rows) (CR.cons bottom row) e1 v0x hBSX s;
      assert (v0 == v0x);
      let hBSX': bigstep (CR.cons v0x row :: CR.zip2_cons vpres rows) e1 v0x = lemma_bigstep_substitute_elim_XMu (row :: rows) e1 (v0x :: vpres) hBSMus
        in

      dstepn_ok (CR.zip2_cons vpres rows) (CR.cons v0x row) e1 v0x hBSX' s;
      assert (v' == v0x);
      bigstep_deterministic hBSMu hBS;
      assert (v == v0x);

      assert (t'.step row s == (s1', v'));

      assert (system_of_exp_invariant (CR.cons v0x row :: CR.zip2_cons vpres rows) e1 s1');
      let s1'': state_of_exp (XMu e1) = coerce_eq () s1' in
      let (| v''', hBSMu''' |) = lemma_bigstep_total (row :: rows) e in
      bigstep_deterministic hBSMu''' hBSMu;
      // assert (v''' == v);
      // assert ([CR.cons v0x row] == CR.zip2_cons [v'''] [row]);
      assert (system_of_exp_invariant (row :: rows) (XMu e1) s1'');
      ()

    | XLet b e1 e2 ->
      let s: state_of_exp e1 & state_of_exp e2 = s in
      let (s1, s2) = s in
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t = dsystem_let (fun i v -> (v, i)) t1 t2 in

      let (s1', v1) = t1.step row s1 in
      let (s2', v2) = t2.step (v1, row) s2 in
      let s' = (s1', s2') in

      let (|v1', hBS1 |) = lemma_bigstep_total (row :: rows) e1 in
      dstepn_ok rows row e1 v1' hBS1 s1;
      assert (v1 == v1');

      let (| v1pres, hBS1s |) = lemma_bigsteps_total rows e1 in
      let v1s = v1 :: v1pres in
      assert_norm (List.Tot.length (row :: rows) == List.Tot.length v1s);
      let rows' = CR.zip2_cons v1s (row :: rows) in
      assert_norm (rows' == (CR.cons v1 row :: CR.zip2_cons v1pres rows));
      let hBS1s: bigsteps (row :: rows) e1 v1s = BSsS _ _ _ _ _ hBS1s hBS1 in
      let hBS2: bigstep rows' e2 v = lemma_bigstep_substitute_elim_XLet (row :: rows) e1 v1s hBS1s e2 v hBS in

      dstepn_ok (CR.zip2_cons v1pres rows) (CR.cons v1 row) e2 v hBS2 s2;
      assert (v2 == v);
      assert (t.step row s == (s', v));
      assert (system_of_exp_invariant (row :: rows) e1 s1');
      assert (system_of_exp_invariant rows' e2 s2');
      assert (system_of_exp_invariant (row :: rows) (XLet b e1 e2) s');
      ()

    | XCheck p e1 e2 ->
      let s: (t.ty_sem t.propty & state_of_exp e1) & state_of_exp e2 = s in
      let ((xp, s1), s2) = s in
      // assert_norm (List.Tot.length (row :: rows) == );

      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let (s1', v1) = t1.step row s1 in
      let (s2', v2) = t2.step row s2 in

      let BSCheck _ _ _ _ _ hBS2 = hBS in
      let (| v1', hBS1 |) = lemma_bigstep_total (row :: rows) e1 in
      // let t = dsystem_then t1 t2 in
      // assert_norm (dsystem_of_exp (XThen e1 e2) == t);
      dstepn_ok rows row e1 v1' hBS1 s1;
      dstepn_ok rows row e2 v hBS2 s2;

      assert (v1 == v1');
      assert (v2 == v);
      assert (system_of_exp_invariant (row :: rows) e1 s1');
      assert (system_of_exp_invariant (row :: rows) e2 s2');
      assert (system_of_exp_invariant (row :: rows) (XCheck p e1 e2) ((v1', s1'), s2'));
      ()


// #pop-options

let rec dstep_many_ok
  (#t: table) (#c: context t)
  (rows: list (row c) { Cons? rows })
  (e: exp t c 'a { causal e })
  (vs: list 'a { List.Tot.length rows == List.Tot.length vs })
  (hBSs: bigsteps rows e vs):
    Tot (s': state_of_exp e { system_of_exp_invariant rows e s' }) (decreases rows) =
  match hBSs with
  | BSsS rows' e vs' r v hBSs' hBS ->
    let t = dsystem_of_exp e in
    (match rows' with
    | [] ->
      let (s', v') = t.step r t.init in
      dstep0_ok r e v hBS;
      s'

    | _ ->
      let s = dstep_many_ok rows' e vs' hBSs' in
      let (s', v') = t.step r s in
      dstepn_ok rows' r e v hBS s;
      s')

#pop-options
#push-options "--fuel 2 --ifuel 1"

let rec dstep_eval_complete'
  (#t: table) (#c: context t)
  (rvs: list (row c & 'a) { Cons? rvs })
  (e: exp t c 'a { causal e })
  (hBSs: bigsteps (List.Tot.map fst rvs) e (List.Tot.map snd rvs)):
    Tot (s': state_of_exp e { system_of_exp_invariant (List.Tot.map fst rvs) e s' /\ xsystem_stepn (system_of_dsystem (dsystem_of_exp e)) rvs s' }) (decreases rvs) =
  let t = dsystem_of_exp e in
  match hBSs with
  | BSsS rows' e vs' r v hBSs' hBS ->
    (match rows' with
    | [] ->
      let (s', v') = t.step r t.init in
      dstep0_ok r e v hBS;
      s'

    | _ ->
      let s = dstep_eval_complete' (List.Tot.tl rvs) e hBSs' in
      let (s', v') = t.step r s in
      dstepn_ok rows' r e v hBS s;
      s')

let dstep_eval_complete
  (#t: table) (#c: context t)
  (rvs: list (row c & 'a))
  (e: exp t c 'a { causal e })
  (hBSs: bigsteps (List.Tot.map fst rvs) e (List.Tot.map snd rvs)):
    Tot (s': state_of_exp e { xsystem_stepn (system_of_dsystem (dsystem_of_exp e)) rvs s' }) (decreases rvs) =
  let t = dsystem_of_exp e in
  match hBSs with
  | BSs0 _ -> t.init
  | BSsS rows' e vs' r v hBSs' hBS ->
    dstep_eval_complete' rvs e hBSs

// let system_eval_complete
//   (rvs: list (row 'c & 'a))
//   (e: exp 'c 'a { causal e })
//   (hBS: bigsteps (List.Tot.map fst rvs) e (List.Tot.map snd rvs)):
//     Lemma (exists (s': state_of_exp e). xsystem_stepn (system_of_dsystem (dsystem_of_exp e)) rvs s') =
//   let s' = dstep_many_ok (List.Tot.map fst rvs) e (List.Tot.map snd rvs) hBS in ()

// let system_eval_complete'
//   (#outer: nat) (#vars: nat)
//   (e: exp { causal e /\ wf e vars })
//   (streams: C.table outer vars)
//   (vs: C.vector value outer)
//   (hBS: bigstep streams e vs):
//     Lemma (exists (s': option (state_of_exp e)). system_stepn' #outer (system_of_exp e vars) (C.Table?._0 streams) vs s') =
//   match outer with
//   | 0 -> assert (system_stepn' (system_of_exp e vars) (C.Table?._0 streams) vs None)
//   | _ -> system_eval_complete e streams vs hBS
*)