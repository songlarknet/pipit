module Pipit.Exp.Causality

open Pipit.Exp.Base
open Pipit.Exp.Subst
open Pipit.Exp.Bigstep

module C = Pipit.Context

(* Causality: does expression `e` have a dependency on the most-recent value of expression `e'`?
    *)
let rec direct_dependency (e e': exp) : bool =
  if e = e' then true
  else
  match e with
  | XVal _ -> false
  | XVar x' -> false
  | XPrim2 _ e1 e2 -> direct_dependency e1 e' || direct_dependency e2 e'
  | XThen e1 e2 -> direct_dependency e1 e' || direct_dependency e2 e'
  | XPre _ -> false
  | XMu e1 -> direct_dependency e1 (lift e' 0)

let rec causal (e: exp): bool =
  match e with
  | XVal _ -> true
  | XVar x' -> true
  | XPrim2 _ e1 e2 -> causal e1 && causal e2
  | XThen e1 e2 -> causal e1 && causal e2
  | XPre e1 -> causal e1
  | XMu e1 -> causal e1 && not (direct_dependency e1 (XVar 0))

// (* Causality: does expression `e` have a dependency on the most-recent value of variable `x`?
//    Non-causal expressions cannot be evaluated with the bigstep semantics. *)
// let rec direct_dependency (e: exp) (x: var) : bool =
//   match e with
//   | XVal _ -> false
//   | XVar x' -> x = x'
//   | XPrim2 _ e1 e2 -> direct_dependency e1 x || direct_dependency e2 x
//   | XThen e1 e2 -> direct_dependency e1 x || direct_dependency e2 x
//   | XPre _ -> false
//   | XMu e1 -> direct_dependency e1 (x + 1)

let rec lift_inj (e e': exp) (x: var):
  Lemma (ensures (e = e') == (lift e x = lift e' x)) =
  match e, e' with
  | XVal _, XVal _ -> ()
  | XVar _, XVar _ -> ()
  | XPrim2 p e1 e2, XPrim2 _ e1' e2' ->
    lift_inj e1 e1' x; lift_inj e2 e2' x
  | XPre e1, XPre e1' -> lift_inj e1 e1' x
  | XThen e1 e2, XThen e1' e2' ->
    lift_inj e1 e1' x; lift_inj e2 e2' x
  | XMu e1, XMu e1' -> lift_inj e1 e1' (x + 1)
  | _, _ -> ()

let rec direct_dependency_lift (e e': exp) (x: var):
    Lemma (ensures direct_dependency e e' == direct_dependency (lift e x) (lift e' x)) (decreases e) =
  lift_inj e e' x;
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 p e1 e2 ->
    direct_dependency_lift e1 e' x;
    direct_dependency_lift e2 e' x;
    ()
  | XPre _ -> ()
  | XThen e1 e2 ->
    direct_dependency_lift e1 e' x;
    direct_dependency_lift e2 e' x;
    ()
  | XMu e1 ->
    direct_dependency_lift e1 (lift e' 0) (x + 1);
    lift_lift_commute e' x 0;
    ()

let rec direct_dependency_subst (x: var) (x': var { x' < x })
  (e: exp { ~ (direct_dependency e (XVar x)) })
  (p: exp { ~ (direct_dependency p (XVar (x - 1))) }):
    Lemma (ensures ~ (direct_dependency (subst e x' p) (XVar (x - 1)))) (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar x'' -> ()
  | XPrim2 prim e1 e2 ->
    direct_dependency_subst x x' e1 p;
    direct_dependency_subst x x' e2 p
  | XPre _ -> ()
  | XThen e1 e2 ->
    direct_dependency_subst x x' e1 p;
    direct_dependency_subst x x' e2 p
  | XMu e1 ->
    direct_dependency_lift p (XVar (x - 1)) 0;
    direct_dependency_subst (x + 1) (x' + 1) e1 (lift p 0)

let rec bigstep_no_dep_no_difference (#outer #inner1 #inner2: nat) (e: exp { ~ (direct_dependency e (XVar inner1)) })
  (streams1: C.table (outer + 1) inner1)
  (streams2: C.table (outer + 1) inner2)
  (row: C.vector value outer) (v v': value)
  (vs: C.vector value (outer + 1))
  (hBS: bigstep
    (C.table_map_append streams1 (C.table_map_append (C.table_of_values (v :: row)) streams2))
    e
    vs):
  Tot (bigstep
        (C.table_map_append streams1 (C.table_map_append (C.table_of_values (v' :: row)) streams2))
        e vs) (decreases hBS) =
  let tv  = C.table_of_values (v :: row) in
  let tv' = C.table_of_values (v' :: row) in
  let t2  = C.table_map_append tv streams2 in
  let t2' = C.table_map_append tv' streams2 in
  let t  = C.table_map_append streams1 t2 in
  let t' = C.table_map_append streams1 t2' in
  match hBS with
  | BSVal _ v ->
    C.table_const_const t t' v;
    BSVal _ v
  | BSVar _ x ->
    assert (x <> inner1);
    if x < inner1
    then
    begin
        C.table_index_append_inner1 streams1 t2 x;
        C.table_index_append_inner1 streams1 t2' x;
        BSVar _ x
    end
    else
    begin
        C.table_index_append_inner2 streams1 t2 x;
        C.table_index_append_inner2 tv streams2 (x - inner1);
        C.table_index_append_inner2 streams1 t2' x;
        C.table_index_append_inner2 tv' streams2 (x - inner1);
        BSVar _ x
    end
  | BSPrim2 _ p e1 e2 vs1 vs2 hBS1 hBS2 ->
    let hBS1' = bigstep_no_dep_no_difference e1 streams1 streams2 row v v' vs1 hBS1 in
    let hBS2' = bigstep_no_dep_no_difference e2 streams1 streams2 row v v' vs2 hBS2 in
    BSPrim2 _ p e1 e2 vs1 vs2 hBS1' hBS2'
  | BSPre s0 ss e1 vs1 hBS1 ->
    let s0' = C.table_hd t' in
    BSPre s0' ss e1 vs1 hBS1
  | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
    let hBS1' = bigstep_no_dep_no_difference e1 streams1 streams2 row v v' vs1 hBS1 in
    let hBS2' = bigstep_no_dep_no_difference e2 streams1 streams2 row v v' vs2 hBS2 in
    BSThen _ e1 e2 vs1 vs2 hBS1' hBS2'
  | BSMu _ e1 vs1 hBS1 ->
    let e1' = subst e1 0 (XMu e1) in
    direct_dependency_subst (inner1 + 1) 0 e1 (XMu e1);
    let hBS1' = bigstep_no_dep_no_difference e1' streams1 streams2 row v v' vs1 hBS1 in
    BSMu _ e1 vs1 hBS1'


let bigstep_recursive_XMu (#outer #inner: nat) (e: exp { causal (XMu e) })
  (streams: C.table (outer + 1) inner)
  (vs: C.vector value outer) (v v': value)
  (hBSmu: bigstep streams (XMu e) (v :: vs)):
    bigstep (C.table_map_append (C.table_of_values (v' :: vs)) streams) e (v :: vs) =
    let hBS' = bigstep_substitute_XMu e streams _ hBSmu in
    C.table_map_append_empty1 (C.table_map_append (C.table_of_values (v :: vs)) streams);
    C.table_map_append_empty1 (C.table_map_append (C.table_of_values (v' :: vs)) streams);
    bigstep_no_dep_no_difference e (C.table_empty (outer + 1)) streams vs v v' (v :: vs) hBS'

