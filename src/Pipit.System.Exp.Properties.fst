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
   It probably doesn't need to take the bigstep relation as input, as we could just
   synthesise it with lemma_bigstep_total as required. In fact, we need to
   synthesise it anyway in some cases.
*)
// let rec system_of_exp_invariant
//   (rows: list (C.row 'c) { Cons? rows })
//   (e: exp 'c 'a { causal e })
//   (v: 'a)
//   (hBS: bigstep rows e v)
//   (s: state_of_exp e):
//     Tot prop (decreases e) =
//   match e with
//   | XVal _ -> unit
//   | XVar _ -> false_elim ()
//   | XBVar _ -> unit
//   | XApp e1 e2 ->
//     assert_norm (causal (XApp e1 e2) == (causal e1 && causal e2));
//     assert_norm (state_of_exp (XApp e1 e2) == (state_of_exp e1 & state_of_exp e2));
//     let s: state_of_exp e1 & state_of_exp e2 = s in
//     let (s1, s2) = s in
//     let BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
//     system_of_exp_invariant rows e1 v1 hBS1 s1 /\
//     system_of_exp_invariant rows e2 v2 hBS2 s2

//   | XFby v1 e2 ->
//     let s: state_of_exp e2 & 'a = s in
//     let (s1, v_buf) = s in
//     let (| v', hBS1' |) = lemma_bigstep_total rows e2 in
//     v_buf == v' /\ system_of_exp_invariant rows e2 v' hBS1' s1

//   | XThen e1 e2 ->
//     let s: system_then_state (state_of_exp e1) (state_of_exp e2) = s in
//     let (| v1, hBS1' |) = lemma_bigstep_total rows e1 in
//     let (| v2, hBS2' |) = lemma_bigstep_total rows e2 in

//     (s.init == false /\ // (List.Tot.length rows = 0) /\
//         system_of_exp_invariant rows e1 v1 hBS1' s.s1 /\
//         system_of_exp_invariant rows e2 v2 hBS2' s.s2)

//   | XMu _ e1 ->
//     let s: state_of_exp e1 = coerce_eq () s in
//     let (| vs, hBSmus |) = lemma_bigsteps_total rows e in
//     let BSsS _ _ _ _ _ _ hBSmu = hBSmus in
//     bigstep_deterministic hBS hBSmu;
//     assert (v == List.Tot.hd vs);

//     let rows' = C.row_zip2_cons vs rows in
//     let hBS' = lemma_bigstep_substitute_elim_XMu rows e1 vs hBSmus in
//     system_of_exp_invariant rows' e1 v hBS' s

//   | XLet b e1 e2 ->
//     let s: state_of_exp e1 & state_of_exp e2 = s in
//     let (s1, s2) = s in
//     let (| vlefts, hBSlefts |) = lemma_bigsteps_total rows e1 in
//     let BSsS _ _ _ _ _ _ hBSleft = hBSlefts in
//     let rows' = C.row_zip2_cons vlefts rows in
//     let hBS': bigstep rows' e2 v = lemma_bigstep_substitute_elim_XLet rows e1 vlefts hBSlefts e2 v hBS in
//     system_of_exp_invariant rows e1 (List.Tot.hd vlefts) hBSleft s1 /\
//       system_of_exp_invariant rows' e2 v hBS' s2

//   | XCheck _ e1 e2 ->
//     let s: (xprop & state_of_exp e1) & state_of_exp e2 = s in
//     let ((xp, s1), s2) = s in
//     let (| v1, hBS1 |) = lemma_bigstep_total rows e1 in
//     let BSCheck _ _ _ _ _ hBS2 = hBS in
//     system_of_exp_invariant rows e1 v1 hBS1 s1 /\
//       system_of_exp_invariant rows e2 v hBS2 s2

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
    system_of_exp_invariant rows e1 s1 /\
      system_of_exp_invariant rows e2 s2

// let dsystem_of_exp_invariant'
//   (rows: list (C.row 'c))
//   (e: exp 'c 'a { causal e })
//   (s: state_of_exp e):
//     prop =
//   match rows with
//   | [] -> s == (dsystem_of_exp e).init
//   | _ :: _ ->
//     let (| v, hBS |) = lemma_bigstep_total rows e in
//     system_of_exp_invariant rows e v hBS s

// let dsystem_of_exp_agrees
//   (rows: list (C.row 'c))
//   (e: exp 'c 'a { causal e })
//   (s0: option (state_of_exp e))
//   (row: C.row 'c)
//   (v: 'a) =
//  let t = dsystem_of_exp e in
//  let s0' =
//     match s0 with
//     | None -> t.init
//     | Some s0' -> s0'
//  in
//  let pre =
//    match s0 with
//    | None -> state_of_exp_invariant rows e v s0'


// let rec dstep0_ok
//   (row: C.row 'c)
//   (e: exp 'c 'a { causal e }):
//     Lemma (ensures (
//       let t = dsystem_of_exp e in
//       let (s', v') = t.step row t.init in
//       v' == (lemma_bigstep_total_v [row] e) /\ system_of_exp_invariant [row] e s'))
//         (decreases e) =
//   match e with
//   | XVal _ -> ()
//   | XBVar _ -> ()
//   | XVar _ -> false_elim ()
//   | XApp e1 e2 ->
//     assert_norm (causal (XApp e1 e2) == (causal e1 && causal e2));
//     assert_norm (state_of_exp (XApp e1 e2) == (state_of_exp e1 & state_of_exp e2));
//     let t1 = dsystem_of_exp e1 in
//     let t2 = dsystem_of_exp e2 in
//     let t  = dsystem_ap2 t1 t2 in
//     assert_norm (dsystem_of_exp (XApp e1 e2) == t);
//     dstep0_ok row e1;
//     dstep0_ok row e2;
//     let (s', v') = t.step row t.init in
//     assert (system_of_exp_invariant [row] e1 (fst s'));
//     assert (system_of_exp_invariant [row] e2 (snd s'));
//     assert_norm (system_of_exp_invariant [row] (XApp e1 e2) s');
//     let (|v, hBS |) = lemma_bigstep_total [row] e in
//     (match hBS with
//     | BSApp _ _ _ _ _ _ _ -> ());
//     assert (v' == v);
//     admit ()
//   | XFby v1 e2 ->
//     let (| v2, hBS2 |) = lemma_bigstep_total [row] e2 in
//     dstep0_ok row e2
//   | XThen e1 e2 ->
//     assert_norm (List.Tot.length [row] == 1);
//     let t1 = dsystem_of_exp e1 in
//     let t2 = dsystem_of_exp e2 in
//     let t = dsystem_then t1 t2 in
//     assert_norm (dsystem_of_exp (XThen e1 e2) == t);
//     // dstep0_ok row e1;
//     // dstep0_ok row e2;
//     // let (s', v') = t.step row t.init in
//     // assert (system_of_exp_invariant [row] e1 s'.s1);
//     // assert (system_of_exp_invariant [row] e2 s'.s2);
//     // assert_norm (system_of_exp_invariant [row] (XThen e1 e2) s');
//     admit ()

//   | _ -> admit ()



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
      // assert (system_of_exp_invariant [row] (XThen e1 e2) s');
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
      let (| vs''', hBSmus''' |) = lemma_bigsteps_total [row] e in
      (match hBSmus''' with | BSsS _ _ _ _ _ (BSs0 _) hBSMu''' ->
        bigstep_deterministic hBSMu''' hBSMu);
      assume ([C.row_cons v0x row] == C.row_zip2_cons vs''' [row]);
      assert (system_of_exp_invariant [row] (XMu e1) s1'');
      ()


//   | XMu _ e1 ->
//     let s: state_of_exp e1 = coerce_eq () s in
//     let (| vs, hBSmus |) = lemma_bigsteps_total rows e in
//     let BSsS _ _ _ _ _ _ hBSmu = hBSmus in
//     bigstep_deterministic hBS hBSmu;
//     assert (v == List.Tot.hd vs);

//     let rows' = C.row_zip2_cons vs rows in
//     let hBS' = lemma_bigstep_substitute_elim_XMu rows e1 vs hBSmus in
//     system_of_exp_invariant rows' e1 v hBS' s

//   | XLet b e1 e2 ->
//     let s: state_of_exp e1 & state_of_exp e2 = s in
//     let (s1, s2) = s in
//     let (| vlefts, hBSlefts |) = lemma_bigsteps_total rows e1 in
//     let BSsS _ _ _ _ _ _ hBSleft = hBSlefts in
//     let rows' = C.row_zip2_cons vlefts rows in
//     let hBS': bigstep rows' e2 v = lemma_bigstep_substitute_elim_XLet rows e1 vlefts hBSlefts e2 v hBS in
//     system_of_exp_invariant rows e1 (List.Tot.hd vlefts) hBSleft s1 /\
//       system_of_exp_invariant rows' e2 v hBS' s2


    | _ -> admit ()




//     Tot (s': state_of_exp e & u: unit { system_of_exp e vars row None s' v /\ system_of_exp_invariant #0 e (C.Table [row]) [v] hBS s' }) (decreases e) =
//   let streams = (C.Table #1 #vars [row]) in
//   match e with
//   | XVal _ -> (| (), () |)
//   | XVar x -> (| (), () |)

//   | XPrim2 p e1 e2 ->
//     let BSPrim2 _ _ _ _ [v1] [v2] hBS1 hBS2 = hBS in
//     let (| s1', () |) = step0_ok e1 row v1 hBS1 in
//     let (| s2', () |) = step0_ok e2 row v2 hBS2 in
//     (| (s1', s2'), () |)

//   | XPre e1 ->
//     let BSPre _ _ _ [] hBS1 = hBS in
//     let v1 = bigstep_monotone_inv_next #0 #vars #streams hBS1 in
//     let hBS1' = bigstep_monotone_inv #0 #vars #streams hBS1 in
//     let (| s1', () |) = step0_ok e1 row v1 hBS1' in
//     (| (s1', v1), () |)

//   | XThen e1 e2 ->
//     let BSThen _ _ _ [v1] [v2] hBS1 hBS2 = hBS in
//     let (| s1', () |) = step0_ok e1 row v1 hBS1 in
//     let (| s2', () |) = step0_ok e2 row v2 hBS2 in
//     (| explicit_cast (state_of_exp e) s2', () |)

//   | XMu e1 ->
//     let hBS' = bigstep_substitute_XMu e1 streams [v] hBS in
//     let (| s1', () |) = step0_ok e1 (C.row_append (C.row1 v) row) v hBS' in
//     (| explicit_cast (state_of_exp e) s1', () |)

// #push-options "--split_queries"
// let rec stepn_ok
//   (#outer: nat { outer > 0 }) (#vars: nat)
//   (e: exp { causal e /\ wf e vars })
//   (row: C.row vars)
//   (streams: C.table outer vars)
//   (v: value)
//   (vs: C.vector value outer)
//   (hBS: bigstep (C.table_append (C.table1 row) streams) e (v :: vs))
//   (s: state_of_exp e)
//   (u: unit { system_of_exp_invariant #(outer - 1) e streams vs (bigstep_monotone #outer hBS) s }):
//     Tot (s': state_of_exp e & u: unit { system_of_exp e vars row (Some s) s' v /\ system_of_exp_invariant #outer e (C.table_append (C.table1 row) streams) (v :: vs) hBS s' }) (decreases e) =
//   let streams' = C.table_append (C.table1 row) streams in
//   match e with
//   | XVal _ -> (| (), () |)
//   | XVar x -> (| (), () |)

//   | XPrim2 p e1 e2 ->
//     let BSPrim2 _ _ _ _ (v1 :: vs1) (v2 :: vs2) hBS1 hBS2 = hBS in
//     let (s1, s2) = s <: (state_of_exp e1 * state_of_exp e2) in
//     let (| s1', () |) = stepn_ok e1 row streams v1 vs1 hBS1 s1 () in
//     let (| s2', () |) = stepn_ok e2 row streams v2 vs2 hBS2 s2 () in
//     (| (s1', s2'), () |)

//   | XPre e1 ->
//     let BSPre _ _ _ (vx :: vs1) hBS1 = hBS in
//     let (s1, v1) = s <: (state_of_exp e1 * value) in
//     let v1' = bigstep_monotone_inv_next #outer #vars #streams' hBS1 in
//     let hBS1' = bigstep_monotone_inv #outer #vars #streams' hBS1 in

//     bigstep_proof_equivalence (bigstep_monotone_inv (bigstep_monotone #(outer - 1) hBS1)) hBS1;
//     bigstep_proof_equivalence hBS1 (bigstep_monotone #outer hBS1');
//     let (| s1', () |) = stepn_ok e1 row streams v1' (v1 :: vs1) hBS1' s1 () in
//     (| (s1', v1'), () |)

//   | XThen e1 e2 ->
//     let BSThen _ _ _ (v1 :: vs1) (v2 :: vs2) hBS1 hBS2 = hBS in
//     let s2 = explicit_cast (state_of_exp e2) s in
//     let (| s2', () |) = stepn_ok e2 row streams v2 vs2 hBS2 s2 () in
//     (| explicit_cast (state_of_exp e) s2', () |)


//   | XMu e1 ->
//     let hBS' = bigstep_substitute_XMu e1 streams' (v :: vs) hBS in
//     let s1 = explicit_cast (state_of_exp e1) s in
//     bigstep_proof_equivalence (bigstep_substitute_XMu e1 streams vs (bigstep_monotone #outer hBS)) (bigstep_monotone #outer (bigstep_substitute_XMu e1 streams' (v :: vs) hBS));
//     let (| s1', () |) = stepn_ok e1 (C.row_append (C.row1 v) row) (C.table_map_append (C.table_of_values vs) streams) v vs hBS' s1 () in
//     (| explicit_cast (state_of_exp e) s1', () |)

// #pop-options

// let rec step_many_ok
//   (#outer: nat { outer > 0 }) (#vars: nat)
//   (e: exp { causal e /\ wf e vars })
//   (streams: C.table outer vars)
//   (vs: C.vector value outer)
//   (hBS: bigstep streams e vs):
//     Tot (s': state_of_exp e & u: unit { system_of_exp_invariant #(outer - 1) e streams vs hBS s' /\ xsystem_stepn #(outer - 1) #vars (system_of_exp e vars) streams vs s' }) (decreases outer) =
//   match streams, vs with
//   | C.Table [row], [v] ->
//     let (| s, () |) = step0_ok e row v hBS in
//     (| s, () |)

//   | C.Table (r :: rs'), v :: vs' ->
//     let (| s, () |) = step_many_ok e (C.Table #(outer - 1) rs') vs' (bigstep_monotone #(outer - 1) hBS) in
//     let (| s', () |) = stepn_ok #(outer - 1) e r (C.Table #(outer - 1) rs') v vs' hBS s () in
//     (| s', () |)

// let system_eval_complete
//   (#outer: nat { outer > 0 }) (#vars: nat)
//   (e: exp { causal e /\ wf e vars })
//   (streams: C.table outer vars)
//   (vs: C.vector value outer)
//   (hBS: bigstep streams e vs):
//     Lemma (exists (s': state_of_exp e). xsystem_stepn #(outer - 1) #vars (system_of_exp e vars) streams vs s') =
//   let (| s', () |) = step_many_ok e streams vs hBS in ()

// let system_eval_complete
//   (#outer: nat) (#vars: nat)
//   (e: exp { causal e /\ wf e vars })
//   (streams: C.table outer vars)
//   (vs: C.vector value outer)
//   (hBS: bigstep streams e vs):
//     Lemma (exists (s': state_of_exp e). xsystem_stepn #outer #vars (system_of_exp e vars) streams vs s') =
//   admit ()

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
