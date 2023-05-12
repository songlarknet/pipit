(*TODO update to typed exprs*)
module Pipit.Exp.Causality

open Pipit.Exp.Base
open Pipit.Exp.Binding
// open Pipit.Exp.Bigstep

module C = Pipit.Context

(* Causality: does expression `e` have a dependency on the most-recent value of expression `e'`?
    *)
let rec direct_dependency (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) : Tot bool (decreases e) =
  match e with
  | XVal _ -> false
  | XVar _ -> false
  | XBVar i' -> i = i'
  | XApp e1 e2 -> direct_dependency e1 i || direct_dependency e2 i
  | XFby _ _ -> false
  | XThen e1 e2 -> direct_dependency e1 i || direct_dependency e2 i
  | XMu _ e1 -> direct_dependency e1 (i + 1)
  | XLet b e1 e2 -> direct_dependency e1 i || direct_dependency e2 (i + 1)
  | XCheck name e1 e2 -> direct_dependency e1 i || direct_dependency e2 i

let rec causal (e: exp 'c 'a): Tot bool (decreases e) =
  match e with
  | XVal _ -> true
  | XVar _ -> true
  | XBVar _ -> true
  | XApp e1 e2 -> causal e1 && causal e2
  | XFby _ e1 -> causal e1
  | XThen e1 e2 -> causal e1 && causal e2
  | XMu _ e1 -> causal e1 && not (direct_dependency e1 0)
  | XLet b e1 e2 -> causal e1 && causal e2
  | XCheck _ e1 e2 -> causal e1 && causal e2

let rec direct_dependency_lift (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) (i': C.index { i' <= List.Tot.length 'c }) (t: Type):
    Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) (i + 1)) (decreases e) =
  admit ()

  // match e with
  // | XVal _ -> ()
  // | XVar _ -> ()
  // | XPrim2 p e1 e2 ->
  //   direct_dependency_lift e1 e' x;
  //   direct_dependency_lift e2 e' x
  // | XIte ep e1 e2 ->
  //   direct_dependency_lift ep e' x;
  //   direct_dependency_lift e1 e' x;
  //   direct_dependency_lift e2 e' x
  // | XPre _ -> ()
  // | XThen e1 e2 ->
  //   direct_dependency_lift e1 e' x;
  //   direct_dependency_lift e2 e' x
  // | XMu e1 ->
  //   direct_dependency_lift e1 (lift e' 0) (x + 1);
  //   lift_lift_commute e' x 0
  // | XLet e1 e2 ->
  //   direct_dependency_lift e1 e' x;
  //   direct_dependency_lift e2 (lift e' 0) (x + 1);
  //   lift_lift_commute e' x 0

let rec direct_dependency_not_subst (i: C.index { C.has_index 'c i }) (i': C.index { i' < i })
  (e: exp 'c 'a { ~ (direct_dependency e i) })
  (p: exp (C.drop1 'c i') (C.get_index 'c i') { ~ (direct_dependency p (i - 1)) }):
    Lemma (ensures ~ (direct_dependency (subst1' e i' p) (i - 1))) (decreases e) =
  admit ()
  // match e with
  // | XVal _ -> ()
  // | XVar x'' -> ()
  // | XPrim2 prim e1 e2 ->
  //   direct_dependency_not_subst x x' e1 p;
  //   direct_dependency_not_subst x x' e2 p
  // | XIte ep e1 e2 ->
  //   direct_dependency_not_subst x x' ep p;
  //   direct_dependency_not_subst x x' e1 p;
  //   direct_dependency_not_subst x x' e2 p
  // | XPre _ -> ()
  // | XThen e1 e2 ->
  //   direct_dependency_not_subst x x' e1 p;
  //   direct_dependency_not_subst x x' e2 p
  // | XMu e1 ->
  //   direct_dependency_lift p (XVar (x - 1)) 0;
  //   direct_dependency_not_subst (x + 1) (x' + 1) e1 (lift p 0)
  // | XLet e1 e2 ->
  //   direct_dependency_lift p (XVar (x - 1)) 0;
  //   direct_dependency_not_subst x x' e1 p;
  //   direct_dependency_not_subst (x + 1) (x' + 1) e2 (lift p 0)

(* Shelve: proofs about causality, will need to be restated on single-element semantics *)

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
  | XLet e1 e2 ->
    direct_dependency_not_subst2 x x' e1 p;
    direct_dependency_not_subst2 (x + 1) (x' + 1) e2 (lift p 0)


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
  | BSLet _ e1 e2 vs2 hBS2 ->
    let e1' = subst e2 0 e1 in
    direct_dependency_not_subst (inner1 + 1) 0 e2 e1;
    let hBS2' = bigstep_no_dep_no_difference e1' streams1 streams2 row v v' vs2 hBS2 in
    BSLet _ e1 e2 vs2 hBS2'


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

// XXX: cannot state this on direct_dependency with var...
// but can state:
let rec direct_dep_XVar__direct_dep_subst (e e': exp) (x: var):
  Lemma (requires direct_dependency e x /\ direct_dependency e' x')
        (ensures direct_dependency (subst e x e') x') =
  admit ()
//
// let rec direct_dep_XVar__direct_dep_subst (e e': exp) (x: var):
//   Lemma (requires direct_dependency e (XVar x))
//         (ensures direct_dependency (subst e x e') e') =
//   match e with
//   | XPrim2 _ e1 e2 ->
//     if direct_dependency e1 (XVar x)
//     then direct_dep_XVar__direct_dep_subst e1 e' x
//     else direct_dep_XVar__direct_dep_subst e2 e' x
//   | XMu e1 ->
//     direct_dep_XVar__direct_dep_subst e1 (lift e' 0) (x + 1)
//   | XThen e1 e2 ->
//     if direct_dependency e1 (XVar x)
//     then direct_dep_XVar__direct_dep_subst e1 e' x
//     else direct_dep_XVar__direct_dep_subst e2 e' x
//   | XLet e1 e2 ->
//     if direct_dependency e1 (XVar x)
//     then direct_dep_XVar__direct_dep_subst e1 e' x
//     else direct_dep_XVar__direct_dep_subst e2 (lift e' 0) (x + 1)
//   | _ -> ()

let causal_subst__causal_XMu (e: exp) (n: nat):
  Lemma (requires causal (XMu e))
        (ensures causal (subst e 0 (XMu e))) =
  assert (not (direct_dependency e (XVar 0)));
  admit ()


let bigstep_recursive_XMu (#outer #inner: nat) (e: exp)
  (streams: C.table (outer + 1) inner)
  (vs: C.vector value outer) (v v': value)
  (hBSmu: bigstep streams (XMu e) (v :: vs)):
    bigstep (C.table_map_append (C.table_of_values (v' :: vs)) streams) e (v :: vs) =
    // bigstep_means_causal_up_to_depth _ _ _ hBSmu;
    let hBS' = bigstep_substitute_XMu e streams _ hBSmu in
    C.table_map_append_empty1 (C.table_map_append (C.table_of_values (v :: vs)) streams);
    C.table_map_append_empty1 (C.table_map_append (C.table_of_values (v' :: vs)) streams);
    bigstep_no_dep_no_difference e (C.table_empty (outer + 1)) streams vs v v' (v :: vs) hBS'


let rec bigstep_empty (inner: nat)
  (e: exp { causal e /\ wf e inner }):
    Tot (bigstep #inner (C.Table []) e []) (decreases e) =
  match e with
  | XVal v -> BSVal _ v
  | XVar x -> BSVar _ x
  | XPre e1 -> BSPre0 e1
  // TODO bigstep_empty XMu: looks pretty true, but needs stronger induction hypothesis.
  // TODO bigstep_empty XLet
  | XMu e1 -> admit ()
  | _ -> admit ()

let rec bigstep_monotone_inv' (#outer #inner: nat)
  (#streams: C.table (outer + 1) inner) (#e: exp { causal e /\ wf e inner }) (#vs: C.vector value outer)
  (hBS: bigstep (C.table_tl streams) e vs):
    Tot (v': value & bigstep streams e (v' :: vs)) (decreases hBS) =
  match hBS with
  | BSVal _ v -> (| v, BSVal _ v |)
  | BSVar _ x -> (| C.row_index (C.table_hd streams) x, BSVar _ x |)
  | BSPrim2 _ p e1 e2 vs1 vs2 hBS1 hBS2 ->
    let (| v1', hBS1' |) = bigstep_monotone_inv' hBS1 in
    let (| v2', hBS2' |) = bigstep_monotone_inv' hBS2 in
    (| eval_prim2 p v1' v2', BSPrim2 _ p e1 e2 (v1' :: vs1) (v2' :: vs2) hBS1' hBS2' |)

  | BSPre r s e1 vs hBS1 ->
    let (| v1', hBS1' |) = bigstep_monotone_inv' #(outer - 1) #inner #(C.table_append (C.table1 r) s) hBS1 in
    (| v1', BSPre (C.table_hd streams) (C.table_tl streams) e1 (v1' :: vs) hBS1' |)

  | BSPre0 e1 ->
    let hBS': bigstep (C.Table []) e1 [] = bigstep_empty inner e1 in
    (| xpre_init, BSPre (C.table_hd streams) (C.Table []) e1 [] hBS' |)

  | BSMu _ e1 vs1 hBS1 ->
    let e1' = subst e1 0 (XMu e1) in
    subst_preserves_wf e1 (XMu e1) inner 0;
    causal_subst__causal_XMu e1 inner;
    let (| v1', hBS1' |) = bigstep_monotone_inv' hBS1 in
      (| v1', BSMu _ e1 (v1' :: vs1) hBS1' |)
  | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
    let (| v1', hBS1' |) = bigstep_monotone_inv' hBS1 in
    let (| v2', hBS2' |) = bigstep_monotone_inv' hBS2 in
    (| (if outer = 0 then v1' else v2'), BSThen _ e1 e2 (v1' :: vs1) (v2' :: vs2) hBS1' hBS2' |)
  | BSLet _ _ _ _ _ -> admit ()




let bigstep_monotone_inv_next (#outer #inner: nat)
  (#streams: C.table (outer + 1) inner) (#e: exp { causal e /\ wf e inner }) (#vs: C.vector value outer)
  (hBS: bigstep (C.table_tl streams) e vs):
    Tot value =
  let (| v', hBS' |) = bigstep_monotone_inv' hBS in v'

let bigstep_monotone_inv (#outer #inner: nat)
  (#streams: C.table (outer + 1) inner) (#e: exp { causal e /\ wf e inner }) (#vs: C.vector value outer)
  (hBS: bigstep (C.table_tl streams) e vs):
    Tot (bigstep streams e (bigstep_monotone_inv_next hBS :: vs)) =
  let (| v', hBS' |) = bigstep_monotone_inv' hBS in hBS'

