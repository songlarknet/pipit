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

let rec causal_up_to_depth (e: exp) (n: nat): bool =
  if n = 0 then true
  else
    match e with
    | XVal _ -> true
    | XVar x' -> true
    | XPrim2 _ e1 e2 -> causal_up_to_depth e1 n && causal_up_to_depth e2 n
    | XThen e1 e2 -> causal_up_to_depth e1 n && causal_up_to_depth e2 n
    | XPre e1 -> causal_up_to_depth e1 (n - 1)
    | XMu e1 -> causal_up_to_depth e1 n && not (direct_dependency e1 (XVar 0))

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

let rec direct_dependency_not_subst (x: var) (x': var { x' < x })
  (e: exp { ~ (direct_dependency e (XVar x)) })
  (p: exp { ~ (direct_dependency p (XVar (x - 1))) }):
    Lemma (ensures ~ (direct_dependency (subst e x' p) (XVar (x - 1)))) (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar x'' -> ()
  | XPrim2 prim e1 e2 ->
    direct_dependency_not_subst x x' e1 p;
    direct_dependency_not_subst x x' e2 p
  | XPre _ -> ()
  | XThen e1 e2 ->
    direct_dependency_not_subst x x' e1 p;
    direct_dependency_not_subst x x' e2 p
  | XMu e1 ->
    direct_dependency_lift p (XVar (x - 1)) 0;
    direct_dependency_not_subst (x + 1) (x' + 1) e1 (lift p 0)

let rec direct_dependency_not_subst2 (x: var) (x': var { x < x' }) (e p: exp):
    Lemma
      (requires not (direct_dependency (subst e x' p) (XVar x)))
      (ensures not (direct_dependency e (XVar x))) (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar x'' -> ()
  | XPrim2 prim e1 e2 ->
    direct_dependency_not_subst2 x x' e1 p;
    direct_dependency_not_subst2 x x' e2 p
  | XPre _ -> ()
  | XThen e1 e2 ->
    direct_dependency_not_subst2 x x' e1 p;
    direct_dependency_not_subst2 x x' e2 p
  | XMu e1 ->
    direct_dependency_lift p (XVar x') 0;
    direct_dependency_not_subst2 (x + 1) (x' + 1) e1 (lift p 0)

let rec causal_up_to_depth_lift (e: exp) (x: var) (n: nat):
    Lemma (ensures causal_up_to_depth e n == causal_up_to_depth (lift e x) n) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 p e1 e2 ->
    causal_up_to_depth_lift e1 x n;
    causal_up_to_depth_lift e2 x n
  | XPre e1 -> if n > 0 then causal_up_to_depth_lift e1 x (n - 1)
  | XThen e1 e2 ->
    causal_up_to_depth_lift e1 x n;
    causal_up_to_depth_lift e2 x n
  | XMu e1 ->
    causal_up_to_depth_lift e1 (x + 1) n;
    lift_lift_commute e1 (x + 1) 0;
    direct_dependency_lift e1 (XVar 0) (x + 1)


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
    direct_dependency_not_subst (inner1 + 1) 0 e1 (XMu e1);
    let hBS1' = bigstep_no_dep_no_difference e1' streams1 streams2 row v v' vs1 hBS1 in
    BSMu _ e1 vs1 hBS1'


(* I originally thought that something like the following should hold:
   if e evaluates to a value, then e is causal
   but this doesn't work for empty input streams, and also doesn't work for
   recursive binders that are nested arbitrarily inside pre combinators, eg
   > pre (pre (pre (pre (mu x. x))))

*)
// let rec bigstep_means_causal (#outer #inner: nat) (e: exp)
//   (streams: C.table outer inner)
//   (vs: C.vector value outer)
//   (hBS: bigstep streams e vs):
//     Lemma (ensures causal e) (decreases hBS) =
//

let rec causal_up_to_subst1 (e e': exp) (x: var) (n: nat):
  Lemma (requires causal_up_to_depth (subst e x e') n)
        (ensures causal_up_to_depth e n) =
  if n = 0 then ()
  else
    match e with
    | XPrim2 _ e1 e2 -> causal_up_to_subst1 e1 e' x n; causal_up_to_subst1 e2 e' x n
    | XMu e1 ->
      causal_up_to_subst1 e1 (lift e' 0) (x + 1) n;
      direct_dependency_not_subst2 0 (x + 1) e1 (lift e' 0);
      ()
    | XPre e1 -> causal_up_to_subst1 e1 e' x (n - 1)
    | XThen e1 e2 -> causal_up_to_subst1 e1 e' x n; causal_up_to_subst1 e2 e' x n
    | _ -> ()

let rec direct_dep_XVar__direct_dep_subst (e e': exp) (x: var):
  Lemma (requires direct_dependency e (XVar x))
        (ensures direct_dependency (subst e x e') e') =
  match e with
  | XPrim2 _ e1 e2 ->
    if direct_dependency e1 (XVar x)
    then direct_dep_XVar__direct_dep_subst e1 e' x
    else direct_dep_XVar__direct_dep_subst e2 e' x
  | XMu e1 ->
    direct_dep_XVar__direct_dep_subst e1 (lift e' 0) (x + 1)
  | XThen e1 e2 ->
    if direct_dependency e1 (XVar x)
    then direct_dep_XVar__direct_dep_subst e1 e' x
    else direct_dep_XVar__direct_dep_subst e2 e' x
  | _ -> ()

let rec direct_dep_acausal__acausal (e e': exp) (n: nat):
  Lemma (requires direct_dependency e e' /\ not (causal_up_to_depth e' n))
        (ensures not (causal_up_to_depth e n)) =
  if e = e' then ()
  else
  match e with
  | XPrim2 p e1 e2 ->
    if direct_dependency e1 e'
    then direct_dep_acausal__acausal e1 e' n
    else direct_dep_acausal__acausal e2 e' n
  | XMu e1 ->
    assert (direct_dependency e1 (lift e' 0));
    causal_up_to_depth_lift e' 0 n;
    direct_dep_acausal__acausal e1 (lift e' 0) n;
    ()
  | XThen e1 e2 ->
    if direct_dependency e1 e'
    then direct_dep_acausal__acausal e1 e' n
    else direct_dep_acausal__acausal e2 e' n
  | _ -> ()

let causal_up_to_depth_subst_XMu (e: exp) (n: nat):
  Lemma (requires causal_up_to_depth (subst e 0 (XMu e)) n)
        (ensures causal_up_to_depth (XMu e) n) =
  if n = 0
  then ()
  else begin
    if direct_dependency e (XVar 0)
    then
    begin
      assert (not (causal_up_to_depth (XMu e) n));
      direct_dep_XVar__direct_dep_subst e (XMu e) 0;
      direct_dep_acausal__acausal (subst e 0 (XMu e)) (XMu e) n;
      ()
    end
    else
      causal_up_to_subst1 e (XMu e) 0 n
  end


let rec bigstep_means_causal_up_to_depth (#outer #inner: nat) (e: exp)
  (streams: C.table outer inner)
  (vs: C.vector value outer)
  (hBS: bigstep streams e vs):
    Lemma (ensures causal_up_to_depth e outer) (decreases hBS) =
  match hBS with
  | BSVal _ _ -> ()
  | BSVar _ x' -> ()
  | BSPrim2 _ p e1' e2' vs1 vs2 hBS1 hBS2 ->
    let XPrim2 _ e1 e2 = e in
    bigstep_means_causal_up_to_depth e1 streams vs1 hBS1;
    bigstep_means_causal_up_to_depth e2 streams vs2 hBS2
  | BSMu _ e1' vs1 hBS1 ->
    let XMu e1 = e in
    bigstep_means_causal_up_to_depth (subst e1 0 (XMu e1)) streams vs1 hBS1;
    causal_up_to_depth_subst_XMu e1 outer
  | BSPre _ streams' e1 vs1 hBS1 ->
    bigstep_means_causal_up_to_depth e1 streams' vs1 hBS1
  | BSPre0 _ -> ()
  | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
    bigstep_means_causal_up_to_depth e1 streams vs1 hBS1;
    bigstep_means_causal_up_to_depth e2 streams vs2 hBS2


let bigstep_recursive_XMu (#outer #inner: nat) (e: exp)
  (streams: C.table (outer + 1) inner)
  (vs: C.vector value outer) (v v': value)
  (hBSmu: bigstep streams (XMu e) (v :: vs)):
    bigstep (C.table_map_append (C.table_of_values (v' :: vs)) streams) e (v :: vs) =
    bigstep_means_causal_up_to_depth _ _ _ hBSmu;
    let hBS' = bigstep_substitute_XMu e streams _ hBSmu in
    C.table_map_append_empty1 (C.table_map_append (C.table_of_values (v :: vs)) streams);
    C.table_map_append_empty1 (C.table_map_append (C.table_of_values (v' :: vs)) streams);
    bigstep_no_dep_no_difference e (C.table_empty (outer + 1)) streams vs v v' (v :: vs) hBS'



let rec bigstep_monotone_inv_next (#outer #inner: nat)
  (#streams: C.table (outer + 1) inner) (#e: exp { causal e }) (#vs: C.vector value outer)
  (hBS1: bigstep (C.table_tl streams) e vs):
    Tot value =
  // TODO prove
  admit ()

let rec bigstep_monotone_inv (#outer #inner: nat)
  (#streams: C.table (outer + 1) inner) (#e: exp { causal e }) (#vs: C.vector value outer)
  (hBS1: bigstep (C.table_tl streams) e vs):
    Tot (bigstep streams e (bigstep_monotone_inv_next hBS1 :: vs)) (decreases hBS1) =
  // TODO prove
  admit ()
