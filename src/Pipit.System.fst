(* Transition systems *)
module Pipit.System

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Causality

module C = Pipit.Context

(* Step functions are relations so that we can express non-deterministic systems.
   The recursive dependency for recursive binders XMu is easier to express as a
   relation too. The result type is `prop`, rather than a computational boolean,
   because composing the relations requires existential quantifiers. *)
type stepfun (input: Type) (state: Type) (result: Type) =
  (* Values of input variables *)
  i: input ->
  (* Starting state, or None for initial *)
  s: option state ->
  (* New state *)
  s': state ->
  (* Return value *)
  r: result ->
  prop

(* A system we get from translating an expression *)
let xsystem (input: nat) (state: Type) = stepfun (C.vector value input) state value

let rec system_of_exp (e: exp) (vars: nat) (#hwf: squash (wf e vars)):
    state: Type & xsystem vars state =
  match e with
  | XVal v ->
    (| unit, (fun i s s' r -> r == v) |)
  | XVar x ->
    (| unit, (fun i s s' r -> r == C.vector_index i x) |)
  | XPrim2 p e1 e2 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    (| st1 * st2, (fun i s (s1', s2') r ->
       let s1, s2 = match s with
         | None -> None, None
         | Some (s1, s2) -> Some s1, Some s2
       in
       exists (r1 r2: value).
             t1 i s1 s1' r1 /\
             t2 i s2 s2' r2 /\
             r == eval_prim2 p r1 r2)
    |)
  | XPre e1 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    (| st1 * value, (fun i s (s1', v') r ->
      let s1, v = match s with
        | None -> None, xpre_init
        | Some (s1, v) -> Some s1, v
      in
      t1 i s1 s1' v' /\ r == v) |)
  | XThen e1 e2 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    (| st2, (fun i s s' r ->
       match s with
       | None -> exists s1' r'. t1 i None s1' r /\ t2 i None s' r'
       | Some _ -> t2 i s s' r)
    |)
  | XMu e1 ->
    let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
    (| st1, (fun (i: C.vector value vars) s s' r ->
      t1 (r :: i) s s' r) |)

let rec stepn
  (#outer #vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (streams: C.table (outer + 1) vars)
  (vs: C.vector value (outer + 1))
  (s': state): prop =
  match streams, vs with
  | C.Table [C.Row row], [r] -> t row None s' r
  | C.Table (C.Row row :: streams'), r :: vs' ->
    exists (s'': state).
      stepn #(outer - 1) e t (C.Table streams') vs' s'' /\
      t row (Some s'') s' r

let rec system_of_exp_invariant
  (#outer #vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (#hwf: squash (wf e vars))
  (#hsys: squash (system_of_exp e vars == (| state, t|)))
  (streams: C.table (outer + 1) vars)
  (vs: C.vector value (outer + 1))
  (hBS: bigstep streams e vs)
  (s: state):
    Tot Type (decreases e) =
  match e with
  | XVar _ -> unit
  | XVal _ -> unit
  | XPrim2 _ e1 e2 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    let (s1, s2) = s <: (st1 * st2) in
    let BSPrim2 _ _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
    system_of_exp_invariant e1 t1 streams vs1 hBS1 s1 *
    system_of_exp_invariant e2 t2 streams vs2 hBS2 s2
  | XPre e1 ->
    let BSPre _ _ _ vs1 hBS1 = hBS in
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (s1, v) = s <: (st1 * value) in
    (hBS': bigstep streams e1 (v :: vs1) * unit)
      // & system_of_exp_invariant #outer #vars e1 t1 streams (v :: vs1) hBS' s1)

  | XThen e1 e2 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    let s2 = s <: st2 in
    let BSThen _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
    system_of_exp_invariant e2 t2 streams vs2 hBS2 s2
  | XMu e1 ->
    let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
    let s1 = s <: st1 in
    let BSMu _ _ vs1 hBS1 = hBS in
    let hBS' = bigstep_substitute_XMu e1 streams vs hBS in
    system_of_exp_invariant #outer #(vars + 1) e1 t1 (C.table_map_append (C.table_of_values vs1) streams) vs1 hBS' s1

let rec step0_ok
  (#vars: nat)
  (#state: Type)
  (e: exp { causal e })
  (t: xsystem vars state)
  (#hwf: squash (wf e vars))
  (#hsys: squash (system_of_exp e vars == (| state, t|)))
  (row: C.vector value vars)
  (v: value)
  (hBS: bigstep (C.Table [C.Row row]) e [v]):
    (s': state & squash (t row None s' v) & system_of_exp_invariant #0 e t (C.Table [C.Row row]) [v] hBS s') =
  match e with
  | XVal _ ->
    (| (), (), () |)

  | XVar x ->
    (| (), (), () |)

  | XPrim2 p e1 e2 ->
    let BSPrim2 _ _ _ _ [v1] [v2] hBS1 hBS2 = hBS in
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    let (| s1', _, ei1 |) = step0_ok e1 t1 row v1 hBS1 in
    let (| s2', _, ei2 |) = step0_ok e2 t2 row v2 hBS2 in
    (| (s1', s2'), (), (ei1, ei2) |)

  | XPre e1 ->
    begin
    match hBS with
    | BSPre _ _ _ [] hBS1 ->
        let (| v1, hBS1' |) = bigstep_monotone_inv #0 #vars #(C.Table [C.Row row]) hBS1 in
        let (| st1, t1 |) = system_of_exp e1 vars in
        let (| s1', _, ei1 |) = step0_ok e1 t1 row v1 hBS1' in
        let s' = (s1', v1) in
        assert (
          system_of_exp_invariant #0 #vars e t (C.Table #1 #vars [C.Row row]) [v] hBS s' ==
          (hBS': bigstep (C.Table #1 #vars [C.Row row]) e1 [v1] * unit));
          // (hBS': bigstep (C.Table [C.Row row]) e1 [v1] & system_of_exp_invariant #0 #vars e1 t1 (C.Table [C.Row row]) [v1] hBS' s1'));
        let h': (hBS': bigstep (C.Table [C.Row row]) e1 [v1] & system_of_exp_invariant #0 #vars e1 t1 (C.Table [C.Row row]) [v1] hBS' s1') =
          (| hBS1', ei1 |) in
        let h'': system_of_exp_invariant #0 #vars e t _ [v] hBS s' =
          ( hBS1', () ) in
        (| s', (), h'' |)

    | _ -> false_elim ()
    end
    // admit ()

  // | XPre e1 ->
  //   let BSPre _ _ _ [] hBS1 = hBS in
  //   let (| v1, hBS1' |) = bigstep_monotone_inv hBS1 in
  //   let (| st1, t1 |) = system_of_exp e1 vars in
  //   let (| s1', _, ei1 |) = step0_ok e1 t1 row v1 hBS1' in
  //   let streams = C.Table [C.Row row] in
  //   let ei1' : system_of_exp_invariant #0 #vars e1 t1 streams [v1] hBS1' s1' = ei1 in
  //   assert (v == xpre_init);
  //   assert (system_of_exp_invariant #0 #vars (XPre e1) t streams [v] hBS (s1', v1) == (hBS': bigstep streams e1 [v1] & system_of_exp_invariant #0 #vars e1 t1 streams [v1] hBS' s1')) by (FStar.Tactics.compute (); FStar.Tactics.dump "ok");
  //   let hb = (| hBS1', ei1' |) <: system_of_exp_invariant (XPre e1) t streams [v] hBS (s1', v1) in
  //   (| (s1', v1), (), (| hBS1', ei1' |) |)

  | _ -> admit ()


let rec stepn_ok
  (#outer #vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (#hwf: squash (wf e vars))
  (#hsys: squash (system_of_exp e vars == (| state, t|)))
  (streams: C.table (outer + 1) vars)
  (vs: C.vector value (outer + 1))
  (hBS: bigstep streams e vs):
    (s': state & squash (stepn e t streams vs s')) =
  match e, streams, vs with
  | XVal _, C.Table [r], [v] ->
    (| (), _ |)
  | XVal _, C.Table (_ :: streams'), v :: vs' ->
    let (| u, _ |) = stepn_ok #(outer - 1) e t (C.Table streams') vs' (bigstep_monotone hBS) in
    (| u, _ |)

  | XVar x, C.Table [r], [v] ->
    (| (), _ |)
  | XVar x, C.Table (_ :: streams'), v :: vs' ->
    let (| u, _ |) = stepn_ok #(outer - 1) e t (C.Table streams') vs' (bigstep_monotone hBS) in (| u, _ |)
  | XPrim2 p e1 e2, C.Table [r], [v] ->
    let BSPrim2 _ _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    let (| s1', _ |) = stepn_ok e1 t1 streams [r1] hBS1 in
    let (| s2', _ |) = stepn_ok e2 t2 streams [r2] hBS2 in
    (| (s1', s2'), _ |)

  | XPrim2 p e1 e2, C.Table (C.Row row :: streams'), v :: vs' ->
    let BSPrim2 _ _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    let (| s, _ |) = stepn_ok #(outer - 1) e t (C.Table streams') vs' (bigstep_monotone hBS) in
    let (s1, s2) = s <: (st1 * st2) in
    let (| s1', _ |) = stepn_ok e1 t1 streams vs1 hBS1 in
    let (| s2', _ |) = stepn_ok e2 t2 streams vs2 hBS2 in
    assert (stepn #(outer - 1) e1 t1 (C.Table streams') (List.Tot.tl vs1) s1);
    assert (v == eval_prim2 p (List.Tot.hd vs1) (List.Tot.hd vs2));
    assert (stepn #(outer - 1) e t (C.Table streams') vs' (s1, s2));
    assert (t1 row (Some s1) s1' (List.Tot.hd vs1));
    assert (t2 row (Some s2) s2' (List.Tot.hd vs2));
    assert (t row (Some s) (s1', s2') v);
    assert (stepn e t streams vs (s1', s2'));
    (| (s1', s2'), _ |)


  // | XVar _, C.Table (_ :: streams'), v :: vs' -> (| (), _ |)
  | _ -> admit ()
  // match streams, vs with
  // | C.Table [C.Row row], [r], [r'] ->
  //   step0_ok e t row r r' s' hBS
  // | C.Table (C.Row row :: streams'), r :: vs_e', r' :: vs_t' ->
  //   admit ()
    // eliminate exists (s_mid: state). stepn #(outer - 1) e t (C.Table streams') vs_t' s_mid
    // returns vs_e == vs_t
    // with hEx.
    //   let hBS' = bigstep_monotone hBS in
    //   let _ = stepn_ok #(outer - 1) e t (C.Table streams') vs_e' vs_t' s_mid hBS' in
    //   match e with
    //   | XVal _ -> ()
    //   | XVar _ -> ()
    //   | XPrim2 p e1 e2 ->
    //     assert (vs_e' == vs_t');
    //     let BSPrim2 _ _ _ _ vs_e1 vs_e2 hBS1 hBS2 = hBS in
    //     let (| st1, t1 |) = system_of_exp e1 vars in
    //     let (| st2, t2 |) = system_of_exp e2 vars in
    //     let (s1, s2)   = s_mid <: (st1 * st2) in
    //     let (s1', s2') = s' <: (st1 * st2) in
    //     eliminate exists (r1' r2': value). t1 row (Some s1) s1' r1' /\ t2 row (Some s2) s2' r2' /\ r' == eval_prim2 p r1' r2'
    //     returns r == r'
    //     with hEx. begin
    //          let _ = stepn_ok e1 t1 streams vs_e1 vs_e1 s1' hBS1 in
    //          let _ = stepn_ok e2 t2 streams vs_e2 vs_e2 s2' hBS2 in
    //          ()
    //          end
    //   | _ -> admit ()
      //   | XPre e1 -> ()
      //   | XThen e1 e2 ->
      //   let BSThen _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
      //   let (| st1, t1 |) = system_of_exp e1 vars in
      //   let (| st2, t2 |) = system_of_exp e2 vars in
      //   eliminate exists (s1': st1) (r2': value). t1 row None s1' r' /\ t2 row None s' r2'
      //   returns r == r'
      //   with hEx. begin
      //        let _ = step0_ok e1 t1 row r1 r' s1' hBS1 in
      //        ()
      //        end
      //   | XMu e1 ->
      //   let BSMu _ _ [r] hBS1 = hBS in
      //   let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
      //   let hBS' = bigstep_recursive_XMu #0 e1 (C.table1 (C.Row row)) [] r r' hBS in
      //   let _ = step0_ok e1 t1 (r' :: row) r r' s' hBS' in
      //   ()



let rec step0_ok
  (#vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (#hwf: squash (wf e vars))
  (#hsys: squash (system_of_exp e vars == (| state, t|)))
  (row: C.vector value vars)
  (r: value)
  (hBS: bigstep (C.table1 (C.Row row)) e (C.vector1 r)):
   Tot (squash (exists (s': state). t row None s' r)) (decreases e) =
 match e with
 | XVal _ -> ()
 | XVar _ -> ()
 | XPrim2 p e1 e2 ->
   let BSPrim2 _ _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
   let (| st1, t1 |) = system_of_exp e1 vars in
   let (| st2, t2 |) = system_of_exp e2 vars in
   let _ = step0_ok e1 t1 row r1 hBS1 in
   let _ = step0_ok e2 t2 row r2 hBS2 in

   eliminate exists (s1' : st1) (s2': st2). t1 row None s1' r1 /\ t2 row None s2' r2 /\ r == eval_prim2 p r1 r2
   returns _ with hEx.
     assert (t row None (s1', s2') r)

 | XPre e1 ->
    begin
   match hBS with
    | BSPre _ _ _ [] hBS1 ->
        let (| st1, t1 |) = system_of_exp e1 vars in
        let _ = step0_ok e1 t1 row r1 hBS1 in

        eliminate exists (s1' : st1). t1 row None s1' r1 /\ r == true
        returns _ with hEx.
            assert (t row None s1' r)
    // | _ -> admit () // false_elim ()
    end
 | _ -> admit ()
 // | XPre e1 -> ()
 // | XThen e1 e2 ->
 //   let BSThen _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
 //   let (| st1, t1 |) = system_of_exp e1 vars in
 //   let (| st2, t2 |) = system_of_exp e2 vars in
 //   eliminate exists (s1': st1) (r2': value). t1 row None s1' r' /\ t2 row None s' r2'
 //   returns r == r'
 //   with hEx. begin
 //     let _ = step0_ok e1 t1 row r1 r' s1' hBS1 in
 //     ()
 //   end
 // | XMu e1 ->
 //   let BSMu _ _ [r] hBS1 = hBS in
 //   let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
 //   let hBS' = bigstep_recursive_XMu #0 e1 (C.table1 (C.Row row)) [] r r' hBS in
 //   let _ = step0_ok e1 t1 (r' :: row) r r' s' hBS' in
 //   ()

// let rec stepn_ok
//   (#outer #vars: nat)
//   (#state: Type)
//   (e: exp)
//   (t: xsystem vars state)
//   (#hwf: squash (wf e vars))
//   (#hsys: squash (system_of_exp e vars == (| state, t|)))
//   (streams: C.table (outer + 1) vars)
//   (vs: C.vector value outer)
//   (r r': value)
//   (s': state)
//   (hBS: bigstep streams e (r :: vs))
//   (#ht: squash (stepn e t streams (r' :: vs) s')):
//    Tot (squash (r == r')) =
//   match streams with
//   | C.Table [C.Row row] ->
//     step0_ok e t row r r' s' hBS
//   | C.Table (C.Row row :: streams') ->
//     eliminate exists (s_mid: state). stepn #(outer - 1) e t (C.Table streams') vs s_mid
//     returns r == r'
//     with hEx.
//       let hBS' = bigstep_monotone hBS in
//       let _ = stepn_ok #(outer - 1) e t (C.Table streams') vs_e' vs_t' s_mid hBS' in
//       match e with
//       | XVal _ -> ()
//       | XVar _ -> ()
//       | XPrim2 p e1 e2 ->
//         let BSPrim2 _ _ _ _ vs_e1 vs_e2 hBS1 hBS2 = hBS in
//         let (| st1, t1 |) = system_of_exp e1 vars in
//         let (| st2, t2 |) = system_of_exp e2 vars in
//         let (s1, s2)   = s_mid <: (st1 * st2) in
//         let (s1', s2') = s' <: (st1 * st2) in
//         eliminate exists (r1' r2': value). t1 row (Some s1) s1' r1' /\ t2 row (Some s2) s2' r2' /\ r' == eval_prim2 p r1' r2'
//         returns r == r'
//         with hEx. begin
//              let _ = stepn_ok e1 t1 streams () r1' s1' hBS1 in
//              let _ = stepn_ok e2 t2 streams r2 r2' s2' hBS2 in
//              ()
//              end
//       | _ -> admit ()
//       //   | XPre e1 -> ()
//       //   | XThen e1 e2 ->
//       //   let BSThen _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
//       //   let (| st1, t1 |) = system_of_exp e1 vars in
//       //   let (| st2, t2 |) = system_of_exp e2 vars in
//       //   eliminate exists (s1': st1) (r2': value). t1 row None s1' r' /\ t2 row None s' r2'
//       //   returns r == r'
//       //   with hEx. begin
//       //        let _ = step0_ok e1 t1 row r1 r' s1' hBS1 in
//       //        ()
//       //        end
//       //   | XMu e1 ->
//       //   let BSMu _ _ [r] hBS1 = hBS in
//       //   let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
//       //   let hBS' = bigstep_recursive_XMu #0 e1 (C.table1 (C.Row row)) [] r r' hBS in
//       //   let _ = step0_ok e1 t1 (r' :: row) r r' s' hBS' in
//       //   ()

let rec stepn_ok
  (#outer #vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (#hwf: squash (wf e vars))
  (#hsys: squash (system_of_exp e vars == (| state, t|)))
  (streams: C.table (outer + 1) vars)
  (vs_e vs_t: C.vector value (outer + 1))
  (s': state)
  (hBS: bigstep streams e vs_e)
  (#ht: squash (stepn e t streams vs_t s')):
   Tot (squash (vs_e == vs_t)) =
  match streams, vs_e, vs_t with
  | C.Table [C.Row row], [r], [r'] ->
    step0_ok e t row r r' s' hBS
  | C.Table (C.Row row :: streams'), r :: vs_e', r' :: vs_t' ->
    eliminate exists (s_mid: state). stepn #(outer - 1) e t (C.Table streams') vs_t' s_mid
    returns vs_e == vs_t
    with hEx.
      let hBS' = bigstep_monotone hBS in
      let _ = stepn_ok #(outer - 1) e t (C.Table streams') vs_e' vs_t' s_mid hBS' in
      match e with
      | XVal _ -> ()
      | XVar _ -> ()
      | XPrim2 p e1 e2 ->
        assert (vs_e' == vs_t');
        let BSPrim2 _ _ _ _ vs_e1 vs_e2 hBS1 hBS2 = hBS in
        let (| st1, t1 |) = system_of_exp e1 vars in
        let (| st2, t2 |) = system_of_exp e2 vars in
        let (s1, s2)   = s_mid <: (st1 * st2) in
        let (s1', s2') = s' <: (st1 * st2) in
        eliminate exists (r1' r2': value). t1 row (Some s1) s1' r1' /\ t2 row (Some s2) s2' r2' /\ r' == eval_prim2 p r1' r2'
        returns r == r'
        with hEx. begin
             let _ = stepn_ok e1 t1 streams vs_e1 vs_e1 s1' hBS1 in
             let _ = stepn_ok e2 t2 streams vs_e2 vs_e2 s2' hBS2 in
             ()
             end
      | _ -> admit ()
      //   | XPre e1 -> ()
      //   | XThen e1 e2 ->
      //   let BSThen _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
      //   let (| st1, t1 |) = system_of_exp e1 vars in
      //   let (| st2, t2 |) = system_of_exp e2 vars in
      //   eliminate exists (s1': st1) (r2': value). t1 row None s1' r' /\ t2 row None s' r2'
      //   returns r == r'
      //   with hEx. begin
      //        let _ = step0_ok e1 t1 row r1 r' s1' hBS1 in
      //        ()
      //        end
      //   | XMu e1 ->
      //   let BSMu _ _ [r] hBS1 = hBS in
      //   let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
      //   let hBS' = bigstep_recursive_XMu #0 e1 (C.table1 (C.Row row)) [] r r' hBS in
      //   let _ = step0_ok e1 t1 (r' :: row) r r' s' hBS' in
      //   ()


 // match e with
 // | XVal _ -> ()
 // | XVar _ -> ()
 // | XPrim2 p e1 e2 ->
 //   let BSPrim2 _ _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
 //   let (| st1, t1 |) = system_of_exp e1 vars in
 //   let (| st2, t2 |) = system_of_exp e2 vars in
 //   let (s1', s2') = s' <: (st1 * st2) in
 //   eliminate exists (r1' r2': value). t1 row None s1' r1' /\ t2 row None s2' r2' /\ r' == eval_prim2 p r1' r2'
 //   returns r == r'
 //   with hEx. begin
 //     let _ = step0_ok e1 t1 row r1 r1' s1' hBS1 in
 //     let _ = step0_ok e2 t2 row r2 r2' s2' hBS2 in
 //     ()
 //   end
 // | XPre e1 -> ()
 // | XThen e1 e2 ->
 //   let BSThen _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
 //   let (| st1, t1 |) = system_of_exp e1 vars in
 //   let (| st2, t2 |) = system_of_exp e2 vars in
 //   eliminate exists (s1': st1) (r2': value). t1 row None s1' r' /\ t2 row None s' r2'
 //   returns r == r'
 //   with hEx. begin
 //     let _ = step0_ok e1 t1 row r1 r' s1' hBS1 in
 //     ()
 //   end
 // | XMu e1 ->
 //   let BSMu _ _ [r] hBS1 = hBS in
 //   let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
 //   let hBS' = bigstep_recursive_XMu #0 e1 (C.table1 (C.Row row)) [] r r' hBS in
 //   let _ = step0_ok e1 t1 (r' :: row) r r' s' hBS' in
 //   ()
