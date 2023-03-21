(* Shelved - translation to transition system with proof *)
module Pipit.System.Exp


// open Pipit.System.Base

// open Pipit.Exp.Base
// open Pipit.Exp.Bigstep
// open Pipit.Exp.Causality

// module C = Pipit.Context

// (* A system we get from translating an expression *)
// let xsystem (input: nat) (state: Type) = system (C.row input) state value

// let xsystem_stepn
//   (#outer #vars: nat)
//   (#state: Type)
//   (t: xsystem vars state)
//   (streams: C.table outer vars)
//   (vs: C.vector value outer)
//   (s': state): prop =
//   let C.Table rs = streams in
//   system_stepn t rs vs s'


// let rec state_of_exp (e: exp): Type =
//   match e with
//   | XVal v -> unit
//   | XVar x -> unit
//   | XPrim2 p e1 e2 -> state_of_exp e1 * state_of_exp e2
//   | XPre e1 -> state_of_exp e1 * value
//   | XThen e1 e2 -> bool * state_of_exp e2
//   | XMu e1 -> state_of_exp e1

// let rec system_of_exp (e: exp) (vars: nat { wf e vars }):
//     xsystem vars (state_of_exp e) =
//   match e with
//   | XVal v -> system_const v
//   | XVar x -> system_map (fun i -> C.row_index i x) system_input
//   | XPrim2 p e1 e2 ->
//     system_map2 (eval_prim2 p) (system_of_exp e1 vars) (system_of_exp e2 vars)
//   | XPre e1 ->
//     system_pre xpre_init (system_of_exp e1 vars)
//   | XThen e1 e2 ->
//     system_then (system_of_exp e1 vars) (system_of_exp e2 vars)
//   | XMu e1 ->
//     let t = system_of_exp e1 (vars + 1) in
//     system_mu #(C.row vars) #(C.row (vars + 1)) (fun i v -> C.row_append (C.row1 v) i) t

// let rec system_of_exp_invariant
//   (#outer #vars: nat)
//   (e: exp { wf e vars /\ causal e })
//   (streams: C.table outer vars)
//   (vs: C.vector value outer)
//   (hBS: bigstep streams e vs)
//   (s: state_of_exp e):
//     Tot prop (decreases e) =
//   match e with
//   | XVar _ -> unit
//   | XVal _ -> unit
//   | XPrim2 _ e1 e2 ->
//     let (s1, s2) = s <: (state_of_exp e1 * state_of_exp e2) in
//     let BSPrim2 _ _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
//     system_of_exp_invariant e1 streams vs1 hBS1 s1 /\
//     system_of_exp_invariant e2 streams vs2 hBS2 s2
//   | XPre e1 ->
//     begin
//     match hBS with
//       | BSPre0 e -> True
//       | BSPre _ _ _ vs1 hBS1 ->
//     let v1'   = bigstep_monotone_inv_next #(outer - 1) #vars #streams hBS1 in
//     let hBS1' = bigstep_monotone_inv #(outer - 1) #vars #streams hBS1 in
//     let (s1, v1) = s <: (state_of_exp e1 * value) in
//     (system_of_exp_invariant #outer #vars e1 streams (v1' :: vs1) hBS1' s1 /\ v1 == v1')
//   end

//   | XThen e1 e2 ->
//     let (init, s2) = coerce_eq #_ #(bool * state_of_exp e2) () s in
//     let BSThen _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
//     (init = (outer > 0)) /\ system_of_exp_invariant e2 streams vs2 hBS2 s2
//   | XMu e1 ->
//     let s1 = coerce_eq #_ #(state_of_exp e1) () s in
//     let BSMu _ _ vs1 hBS1 = hBS in
//     let hBS' = bigstep_substitute_XMu e1 streams vs hBS in
//     system_of_exp_invariant #outer #(vars + 1) e1 (C.table_map_append (C.table_of_values vs1) streams) vs1 hBS' s1

// TODO temp disable proof while simplifying transform
// let rec step0_ok
//   (#vars: nat)
//   (e: exp { causal e /\ wf e vars })
//   (row: C.row vars)
//   (v: value)
//   (hBS: bigstep (C.Table [row]) e [v]):
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
