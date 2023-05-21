(* Shelved - translation to transition system proof *)
module Pipit.System.Exp.Properties

module C = Pipit.Context

open Pipit.System.Base
open Pipit.System.Exp
open Pipit.System.Det

open Pipit.Exp

#push-options "--split_queries always"
#push-options "--fuel 1 --ifuel 1"

(*
   The invariant describes the transition system's state after it has been fed with all of `rows` as inputs.
*)
let rec system_of_exp_invariant
  (rows: list (C.row 'c) { Cons? rows })
  (e: exp 'c 'a { causal e })
  (s: state_of_exp e):
    Tot prop (decreases e) =
  match e with
  | XVal _ -> True
  | XVar _ -> false_elim ()
  | XBVar _ -> True
  | XApp e1 e2 ->
    assert_norm (causal (XApp e1 e2) == (causal e1 && causal e2));
    assert_norm (state_of_exp (XApp e1 e2) == (state_of_exp e1 & state_of_exp e2));
    let s: state_of_exp e1 & state_of_exp e2 = s in
    let (s1, s2) = s in
    system_of_exp_invariant rows e1 s1 /\
    system_of_exp_invariant rows e2 s2

  | XFby v1 e2 ->
    let s: state_of_exp e2 & 'a = s in
    let (s1, v_buf) = s in
    let v = lemma_bigstep_total_v rows e2 in
    v_buf == v /\ system_of_exp_invariant rows e2 s1

  | XThen e1 e2 ->
    let s: system_then_state (state_of_exp e1) (state_of_exp e2) = s in
    (s.init == false /\
        system_of_exp_invariant rows e1 s.s1 /\
        system_of_exp_invariant rows e2 s.s2)

  | XMu _ e1 ->
    let s: state_of_exp e1 = coerce_eq () s in
    let (| vs, hBSmus |) = lemma_bigsteps_total rows e in
    let rows' = C.row_zip2_cons vs rows in
    system_of_exp_invariant rows' e1 s

  | XLet b e1 e2 ->
    let s: state_of_exp e1 & state_of_exp e2 = s in
    let (s1, s2) = s in
    let (| vlefts, hBSlefts |) = lemma_bigsteps_total rows e1 in
    let rows' = C.row_zip2_cons vlefts rows in
    system_of_exp_invariant rows e1 s1 /\
      system_of_exp_invariant rows' e2 s2

  | XCheck _ e1 e2 ->
    let s: (xprop & state_of_exp e1) & state_of_exp e2 = s in
    let ((xp, s1), s2) = s in
    xp == lemma_bigstep_total_v rows e1 /\
      system_of_exp_invariant rows e1 s1 /\
      system_of_exp_invariant rows e2 s2

let rec dstep0_ok
    (row: C.row 'c)
    (e: exp 'c 'a { causal e })
    (v: 'a)
    (hBS: bigstep [row] e v):
      Lemma (ensures (
        let t = dsystem_of_exp e in
        let (s', v') = t.step row t.init in
        v == v' /\ system_of_exp_invariant [row] e s'))
          (decreases e) =
    match e with
    | XVal _ -> ()
    | XBVar _ -> ()
    | XVar _ -> false_elim ()
    | XApp e1 e2 ->
      assert_norm (causal (XApp e1 e2) == (causal e1 && causal e2));
      assert_norm (state_of_exp (XApp e1 e2) == (state_of_exp e1 & state_of_exp e2));
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t  = dsystem_ap2 t1 t2 in
      assert_norm (dsystem_of_exp (XApp e1 e2) == t);
      let BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
      dstep0_ok row e1 v1 hBS1;
      dstep0_ok row e2 v2 hBS2;
      let (s', v') = t.step row t.init in
      assert_norm (system_of_exp_invariant [row] (XApp e1 e2) s')
    | XFby v1 e2 ->
      let (| v2, hBS2 |) = lemma_bigstep_total [row] e2 in
      dstep0_ok row e2 v2 hBS2
    | XThen e1 e2 ->
      assert_norm (List.Tot.length [row] == 1);
      let BSThen1 _ _ _ _ hBS1 = hBS in
      let (| v2, hBS2 |) = lemma_bigstep_total [row] e2 in
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t = dsystem_then t1 t2 in
      assert_norm (dsystem_of_exp (XThen e1 e2) == t);
      dstep0_ok row e1 v hBS1;
      dstep0_ok row e2 v2 hBS2;
      let (s', v') = t.step row t.init in
      assert (system_of_exp_invariant [row] e1 s'.s1);
      assert (system_of_exp_invariant [row] e2 s'.s2);
      assert (s'.init == false);
      ()

    | XMu _ e1 ->
      let t1 = dsystem_of_exp e1 in
      let t = dsystem_mu_causal #(C.row 'c) #('a & C.row 'c) (fun i v -> (v, i)) t1 in

      let bottom = Pipit.Inhabited.get_inhabited <: 'a in
      let (s_scrap, v0) = t1.step (bottom, row) t1.init in
      let (s1', v') = t1.step (v0, row) t1.init in

      let hBSs0: bigsteps [] (XMu e1) [] = BSs0 (XMu e1) in
      let (|v0x, hBSX |) = lemma_bigstep_total [C.row_cons bottom row] e1 in
      let hBSMu: bigstep [row] (XMu e1) v0x = lemma_bigstep_substitute_intros_XMu [] e1 [] row v0x bottom hBSs0 hBSX in
      let hBSMus: bigsteps [row] (XMu e1) [v0x] = BSsS _ _ _ _ _ hBSs0 hBSMu in

      dstep0_ok (C.row_cons bottom row) e1 v0x hBSX;
      assert (v0 == v0x);
      let hBSX': bigstep [C.row_cons v0x row] e1 v0x = lemma_bigstep_substitute_elim_XMu [row] e1 [v0x] hBSMus
        in

      dstep0_ok (C.row_cons v0x row) e1 v0x hBSX';
      assert (v' == v0x);
      bigstep_deterministic hBSMu hBS;
      assert (v == v0x);

      assert (t.step row t.init == (s1', v'));

      assert (system_of_exp_invariant [C.row_cons v0x row] e1 s1');
      let s1'': state_of_exp (XMu e1) = coerce_eq () s1' in
      let (| v''', hBSMu''' |) = lemma_bigstep_total [row] e in
      bigstep_deterministic hBSMu''' hBSMu;
      // assert (v''' == v);
      // assert ([C.row_cons v0x row] == C.row_zip2_cons [v'''] [row]);
      assert (system_of_exp_invariant [row] (XMu e1) s1'');
      ()

    | XLet b e1 e2 ->
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t = dsystem_let #(C.row 'c) #(b & C.row 'c) (fun i v -> (v, i)) t1 t2 in

      let (s1', v1) = t1.step row t1.init in
      let (s2', v2) = t2.step (v1, row) t2.init in
      let s' = (s1', s2') in

      let (|v1', hBS1 |) = lemma_bigstep_total [row] e1 in
      dstep0_ok row e1 v1' hBS1;
      assert (v1 == v1');

      let v1s = [v1] in
      assert_norm (List.Tot.length [row] == 1);
      assert_norm (List.Tot.length v1s == 1);
      let rows' = C.row_zip2_cons v1s [row] in
      assert_norm (rows' == [C.row_cons v1 row]);
      let hBS1s: bigsteps [row] e1 v1s = BSsS _ _ _ _ _ (BSs0 e1) hBS1 in
      let hBS2: bigstep rows' e2 v = lemma_bigstep_substitute_elim_XLet [row] e1 v1s hBS1s e2 v hBS in

      let (| vlefts, hBSlefts |) = lemma_bigsteps_total [row] e1 in
      (match hBSlefts with
       | BSsS _ _ _ _ _ hBSlefts' hBSleft ->
        match hBSlefts' with
        | BSs0 _ ->
        bigstep_deterministic hBSleft hBS1;
        assert (vlefts == v1s)
      );

      dstep0_ok (C.row_cons v1 row) e2 v hBS2;
      assert (v2 == v);
      assert (t.step row t.init == (s', v));
      assert (system_of_exp_invariant [row] e1 s1');
      assert (system_of_exp_invariant rows' e2 s2');
      assert (system_of_exp_invariant [row] (XLet b e1 e2) s');
      ()


    | XCheck _ e1 e2 ->
      assert_norm (List.Tot.length [row] == 1);

      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let (s1', v1) = t1.step row t1.init in
      let (s2', v2) = t2.step row t2.init in

      let BSCheck _ _ _ _ _ hBS2 = hBS in
      let (| v1', hBS1 |) = lemma_bigstep_total [row] e1 in
      // let t = dsystem_then t1 t2 in
      // assert_norm (dsystem_of_exp (XThen e1 e2) == t);
      dstep0_ok row e1 v1' hBS1;
      dstep0_ok row e2 v hBS2;

      assert (v1 == v1');
      assert (v2 == v);
      assert (system_of_exp_invariant [row] e1 s1');
      assert (system_of_exp_invariant [row] e2 s2');
      ()

let rec dstepn_ok
    (rows: list (C.row 'c) { Cons? rows })
    (row: C.row 'c)
    (e: exp 'c 'a { causal e })
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

    | XMu _ e1 ->
      assert_norm (state_of_exp (XMu e1) == state_of_exp e1);
      let s: state_of_exp (XMu e1) = s in
      let s: state_of_exp e1 = coerce_eq () s in
      let t1 = dsystem_of_exp e1 in
      let t = dsystem_mu_causal #(C.row 'c) #('a & C.row 'c) (fun i v -> (v, i)) t1 in

      let bottom = Pipit.Inhabited.get_inhabited <: 'a in
      let (s_scrap, v0) = t1.step (bottom, row) s in
      let (s1', v') = t1.step (v0, row) s in

      let (| vpres, hBSs|) = lemma_bigsteps_total rows (XMu e1) in
      let (| v0x, hBSX |) = lemma_bigstep_total (C.row_zip2_cons (bottom :: vpres) (row :: rows)) e1 in
      let hBSMu: bigstep (row :: rows) (XMu e1) v0x = lemma_bigstep_substitute_intros_XMu rows e1 vpres row v0x bottom hBSs hBSX in
      let hBSMus: bigsteps (row :: rows) (XMu e1) (v0x :: vpres) = BSsS _ _ _ _ _ hBSs hBSMu in

      dstepn_ok (C.row_zip2_cons vpres rows) (C.row_cons bottom row) e1 v0x hBSX s;
      assert (v0 == v0x);
      let hBSX': bigstep (C.row_cons v0x row :: C.row_zip2_cons vpres rows) e1 v0x = lemma_bigstep_substitute_elim_XMu (row :: rows) e1 (v0x :: vpres) hBSMus
        in

      dstepn_ok (C.row_zip2_cons vpres rows) (C.row_cons v0x row) e1 v0x hBSX' s;
      assert (v' == v0x);
      bigstep_deterministic hBSMu hBS;
      assert (v == v0x);

      assert (t.step row s == (s1', v'));

      assert (system_of_exp_invariant (C.row_cons v0x row :: C.row_zip2_cons vpres rows) e1 s1');
      let s1'': state_of_exp (XMu e1) = coerce_eq () s1' in
      let (| v''', hBSMu''' |) = lemma_bigstep_total (row :: rows) e in
      bigstep_deterministic hBSMu''' hBSMu;
      // assert (v''' == v);
      // assert ([C.row_cons v0x row] == C.row_zip2_cons [v'''] [row]);
      assert (system_of_exp_invariant (row :: rows) (XMu e1) s1'');
      ()

    | XLet b e1 e2 ->
      let s: state_of_exp e1 & state_of_exp e2 = s in
      let (s1, s2) = s in
      let t1 = dsystem_of_exp e1 in
      let t2 = dsystem_of_exp e2 in
      let t = dsystem_let #(C.row 'c) #(b & C.row 'c) (fun i v -> (v, i)) t1 t2 in

      let (s1', v1) = t1.step row s1 in
      let (s2', v2) = t2.step (v1, row) s2 in
      let s' = (s1', s2') in

      let (|v1', hBS1 |) = lemma_bigstep_total (row :: rows) e1 in
      dstepn_ok rows row e1 v1' hBS1 s1;
      assert (v1 == v1');

      let (| v1pres, hBS1s |) = lemma_bigsteps_total rows e1 in
      let v1s = v1 :: v1pres in
      assert_norm (List.Tot.length (row :: rows) == List.Tot.length v1s);
      let rows' = C.row_zip2_cons v1s (row :: rows) in
      assert_norm (rows' == (C.row_cons v1 row :: C.row_zip2_cons v1pres rows));
      let hBS1s: bigsteps (row :: rows) e1 v1s = BSsS _ _ _ _ _ hBS1s hBS1 in
      let hBS2: bigstep rows' e2 v = lemma_bigstep_substitute_elim_XLet (row :: rows) e1 v1s hBS1s e2 v hBS in

      dstepn_ok (C.row_zip2_cons v1pres rows) (C.row_cons v1 row) e2 v hBS2 s2;
      assert (v2 == v);
      assert (t.step row s == (s', v));
      assert (system_of_exp_invariant (row :: rows) e1 s1');
      assert (system_of_exp_invariant rows' e2 s2');
      assert (system_of_exp_invariant (row :: rows) (XLet b e1 e2) s');
      ()

    | XCheck p e1 e2 ->
      let s: (xprop & state_of_exp e1) & state_of_exp e2 = s in
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
  (rows: list (C.row 'c) { Cons? rows })
  (e: exp 'c 'a { causal e })
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
  (rvs: list (C.row 'c & 'a) { Cons? rvs })
  (e: exp 'c 'a { causal e })
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
  (rvs: list (C.row 'c & 'a))
  (e: exp 'c 'a { causal e })
  (hBSs: bigsteps (List.Tot.map fst rvs) e (List.Tot.map snd rvs)):
    Tot (s': state_of_exp e { xsystem_stepn (system_of_dsystem (dsystem_of_exp e)) rvs s' }) (decreases rvs) =
  let t = dsystem_of_exp e in
  match hBSs with
  | BSs0 _ -> t.init
  | BSsS rows' e vs' r v hBSs' hBS ->
    dstep_eval_complete' rvs e hBSs

// let system_eval_complete
//   (rvs: list (C.row 'c & 'a))
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
