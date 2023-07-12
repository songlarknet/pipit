(* Causality is whether a program can be scheduled without depending on future
   values. The causality check just requires any references to recursive binders
   to be "guarded" by a delay.

   The following is bad:
   > rec x. x + 1             (XMu (XApp (+1) x))
   But adding a delay fixes it:
   > rec x. 0 fby (x + 1)     (XMu (XFby 0 (XApp (+1) x)))

*)
module Pipit.Exp.Causality

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.Exp.Binding
open Pipit.Exp.Binding.Properties
open Pipit.Exp.Bigstep

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties

(* Direct dependencies: does expression `e` have a non-delayed dependency on bound-variable `i`?
    *)
let rec direct_dependency (e: exp 'c 'a) (i: C.index) : Tot bool (decreases e) =
  match e with
  | XVal _ -> false
  | XVar _ -> false
  | XBVar i' -> i = i'
  | XApp e1 e2 -> direct_dependency e1 i || direct_dependency e2 i
  | XFby _ _ -> false
  | XThen e1 e2 -> direct_dependency e1 i || direct_dependency e2 i
  | XMu _ e1 -> direct_dependency e1 (i + 1)
  (* This is more restrictive than necessary. The following should work:
     > rec x. let y = x + 1 in 0 fby y
     Maybe the definition should allow `e1` to directly refer to `i` if `e2` does
     not directly refer to `e1`:
     > XLet b e1 e2 ->
     >    (if direct_dependency e1 i then direct_dependency e2 0 else false) ||
     >        direct_dependency e2 (i + 1)
  *)
  | XLet b e1 e2 -> direct_dependency e1 i || direct_dependency e2 (i + 1)
  | XCheck name e1 e2 -> direct_dependency e1 i || direct_dependency e2 i

(* Causality: are all references to recursive streams delayed?
   All causal expressions make progress.
   We also sneak in a well-formedness check here that there are no free
   variables. This is really a different check, but it's convenient.
*)
let rec causal (e: exp 'c 'a): Tot bool (decreases e) =
  match e with
  | XVal _ -> true
  | XVar _ -> false // no free variables
  | XBVar _ -> true
  | XApp e1 e2 -> causal e1 && causal e2
  | XFby _ e1 -> causal e1
  | XThen e1 e2 -> causal e1 && causal e2
  | XMu _ e1 -> causal e1 && not (direct_dependency e1 0)
  | XLet b e1 e2 -> causal e1 && causal e2
  | XCheck _ e1 e2 -> causal e1 && causal e2

#push-options "--fuel 1 --ifuel 1"

#push-options "--split_queries always"

(* not used, but lemma_direct_dependency_not_subst' needs i' < i case *)
let rec lemma_direct_dependency_lift_ge (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) (i': C.index { i >= i' /\ i' <= List.Tot.length 'c }) (t: Type):
    Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) (i + 1)) (decreases e) =
  match e with
  | XVal _ | XVar _ | XBVar _ -> ()
  | XApp e1 e2 ->
    lemma_direct_dependency_lift_ge e1 i i' t;
    lemma_direct_dependency_lift_ge e2 i i' t;
    assert_norm (direct_dependency (XApp e1 e2) i == (direct_dependency e1 i || direct_dependency e2 i));
    assert_norm (direct_dependency (lift1' (XApp e1 e2) i' t) (i + 1) == (direct_dependency (lift1' e1 i' t) (i + 1) || direct_dependency (lift1' e2 i' t) (i + 1)));
    ()
  | XFby _ e1 -> lemma_direct_dependency_lift_ge e1 i i' t
  | XThen e1 e2 ->
    lemma_direct_dependency_lift_ge e1 i i' t;
    lemma_direct_dependency_lift_ge e2 i i' t
  | XMu _ e1 ->
    lemma_direct_dependency_lift_ge e1 (i + 1) (i' + 1) t
  | XLet b e1 e2 ->
    lemma_direct_dependency_lift_ge e1 i i' t;
    lemma_direct_dependency_lift_ge e2 (i + 1) (i' + 1) t
  | XCheck _ e1 e2 ->
    lemma_direct_dependency_lift_ge e1 i i' t;
    lemma_direct_dependency_lift_ge e2 i i' t

// let rec lemma_direct_dependency_lift_lt (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) (i': C.index { i < i' /\ i' <= List.Tot.length 'c }) (t: Type):
//     Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) i) (decreases e) =
//   match e with
//   | XVal _ | XVar _ | XBVar _ -> ()
//   | XMu _ e1 ->
//     lemma_direct_dependency_lift_lt e1 (i + 1) (i' + 1) t

(* used by lemma_bigstep_substitute_intros_no_dep *)
let rec lemma_direct_dependency_not_subst' (i: C.index) (i': C.index { C.has_index 'c i' /\ i' <= i })
  (e: exp 'c 'a { ~ (direct_dependency e (i + 1)) })
  (p: exp (C.drop1 'c i') (C.get_index 'c i') { ~ (direct_dependency p i ) }):
    Lemma
      (requires (C.has_index (C.drop1 'c i') i))
      (ensures ~ (direct_dependency (subst1' e i' p) i)) (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar _ -> ()
  | XApp e1 e2 ->
    assert_norm (direct_dependency (XApp e1 e2) (i + 1) == (direct_dependency e1 (i + 1) || direct_dependency e2 (i + 1)));
    lemma_direct_dependency_not_subst' i i' e1 p;
    lemma_direct_dependency_not_subst' i i' e2 p;
    assert_norm (subst1' (XApp e1 e2) i' p == XApp (subst1' e1 i' p) (subst1' e2 i' p));
    assert_norm (direct_dependency (subst1' (XApp e1 e2) i' p) i == (direct_dependency (subst1' e1 i' p) i || direct_dependency (subst1' e2 i' p) i));
    ()
  | XFby v1 e2 ->
    ()
  | XThen e1 e2 ->
    lemma_direct_dependency_not_subst' i i' e1 p;
    lemma_direct_dependency_not_subst' i i' e2 p
  | XMu _ e1 ->
    lemma_direct_dependency_lift_ge p i 0 'a;
    lemma_direct_dependency_not_subst' (i + 1) (i' + 1) e1 (lift1 p 'a)
  | XLet b e1 e2 ->
    lemma_direct_dependency_not_subst' i i' e1 p;
    lemma_direct_dependency_lift_ge p i 0 b;
    lemma_direct_dependency_not_subst' (i + 1) (i' + 1) e2 (lift1 p b)
  | XCheck _ e1 e2 ->
    lemma_direct_dependency_not_subst' i i' e1 p;
    lemma_direct_dependency_not_subst' i i' e2 p

#push-options "--fuel 1 --ifuel 1"

(* used by lemma_bigstep_substitute_elim_XMu, indirectly by transition system proof *)
let rec lemma_bigstep_substitute_elim
  (i: C.index { i < List.Tot.length 'c })
  (rows: list (C.row (C.drop1 'c i)) { Cons? rows })
  (e: exp (C.drop1 'c i) (C.get_index 'c i))
  (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp 'c 'a)
  (v': 'a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep rows (subst1' e' i e) v'):
    Tot (bigstep (C.row_zip2_lift1_dropped i rows vs) e' v') (decreases hBSe') =
  let latest = List.Tot.hd rows in
  let rows' = C.row_zip2_lift1_dropped i rows vs in
  let latest' = List.Tot.hd rows' in
  match e' with
  | XVal v -> BSVal _ _
  | XVar _ -> false_elim ()
  | XBVar i' ->
    if i = i'
    then
      (match hBSse with
       | BSsS r e_ _ _ v hBSsep hBSe ->
         bigstep_deterministic hBSe hBSe';
         BSVar latest' (List.Tot.tl rows') i)
    else
      (match hBSe' with
       | BSVar latest prefix ix ->
         BSVar latest' (List.Tot.tl rows') i')
  | XApp e1 e2 ->
    (match hBSe' with
    | BSApp _ _ _ v1 v2 hBS1 hBS2 ->
      assert_norm (subst1' (XApp e1 e2) i e == XApp (subst1' e1 i e) (subst1' e2 i e));
      let hBS1' = lemma_bigstep_substitute_elim i rows e vs e1 v1 hBSse hBS1 in
      let hBS2' = lemma_bigstep_substitute_elim i rows e vs e2 v2 hBSse hBS2 in
      BSApp _ _ _ v1 v2 hBS1' hBS2')
  | XFby v1 e2 ->
    (match hBSe' with
    | BSFby1 _ _ _ -> BSFby1 _ v1 e2
    | BSFbyS latest prefix _ v2 _ hBS2 ->
      let BSsS _ _ vs' _ _ hBSse' _ = hBSse in
      let hBS2' = lemma_bigstep_substitute_elim i prefix e vs' e2 v2 hBSse' hBS2 in
      BSFbyS latest' (List.Tot.tl rows') v1 v2 e2 hBS2')
  | XThen e1 e2 ->
    (match hBSe' with
    | BSThen1 _ _ _ _ hBS1 ->
      let hBS1' = lemma_bigstep_substitute_elim i rows e vs e1 v' hBSse hBS1 in
      BSThen1 _ e1 e2 _ hBS1'
    | BSThenS _ _ _ _ hBS2 ->
      let hBS2' = lemma_bigstep_substitute_elim i rows e vs e2 v' hBSse hBS2 in
      BSThenS _ e1 e2 _ hBS2')
  | XMu _ e1 ->
    (match hBSe' with
    | BSMu _ _ e1' _ hBSe1 ->
      C.lemma_dropCons 'a 'c (i + 1);
      assert (C.drop1 ('a :: 'c) (i + 1) == 'a :: C.drop1 'c i);
      let lifted: exp (C.drop1 ('a :: 'c) (i + 1)) (C.get_index ('a :: 'c) (i + 1)) = lift1 e 'a in
      assert_norm (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) lifted));

      let se: exp ('a :: C.drop1 'c i) 'a = e1' in
      let se: exp (C.drop1 'c i) 'a = subst1 e1' (XMu e1') in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert (subst1 (subst1' e1 (i + 1) lifted) (XMu e1') == subst1' (subst1 e1 (XMu e1)) i e);
      let hBSe1': bigstep rows se v' = hBSe1 in
      let hBSX = lemma_bigstep_substitute_elim i rows e vs (subst1 e1 (XMu e1)) v' hBSse hBSe1' in
      BSMu _ _ e1 _ hBSX)
  | XLet b e1 e2 ->
    (match hBSe' with
    | BSLet _ e1' e2' _ hBSe1' ->
      C.lemma_dropCons b 'c (i + 1);
      assert (C.drop1 (b :: 'c) (i + 1) == b :: C.drop1 'c i);
      C.lemma_get_index_Cons b 'c i;
      let lifted: exp (C.drop1 (b :: 'c) (i + 1)) (C.get_index (b :: 'c) (i + 1)) = lift1 e b in
      assert_norm (subst1' (XLet b e1 e2) i e == XLet b (subst1' e1 i e) (subst1' e2 (i + 1) lifted));

      lemma_subst_subst_distribute_le e2 0 i e1 e;
      let hBSX = lemma_bigstep_substitute_elim i rows e vs (subst1 e2 e1) v' hBSse hBSe1' in
      BSLet _ e1 e2 _ hBSX)
  | XCheck p e1 e2 ->
    (match hBSe' with
    | BSCheck _ _ _ _ _ hBS1 ->
      let hBS1' = lemma_bigstep_substitute_elim i rows e vs e2 v' hBSse hBS1 in
      BSCheck _ p e1 e2 _ hBS1')

(* used by lemma_bigstep_substitute_intros_no_dep, indirectly by lemma_bigstep_total *)
let rec lemma_bigstep_substitute_intros
  (i: C.index { i < List.Tot.length 'c })
  (rows: list (C.row (C.drop1 'c i)) { Cons? rows })
  (e: exp (C.drop1 'c i) (C.get_index 'c i))
  (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp 'c 'a)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep (C.row_zip2_lift1_dropped i rows vs) e' a):
    Tot (bigstep rows (subst1' e' i e) a) (decreases hBSe') =
  let row = List.Tot.hd rows in
  let rows' = List.Tot.tl rows in
  match e' with
  | XVal _ -> BSVal _ _
  | XVar _ -> false_elim ()
  | XBVar i' ->
    if i = i'
    then (let BSsS _ _ _ _ _ _ hBSe = hBSse in hBSe)
    else if i' < i
    then BSVar row rows' i'
    else (
      C.lemma_drop_get_index_gt 'c i (i' - 1);
      assert (C.opt_index (C.drop1 'c i) (i' - 1) == Some 'a);
      assert_norm (subst1' (XBVar i') i e == XBVar #(C.drop1 'c i) #('a) (i' - 1));
      BSVar row rows' (i' - 1))
  | XApp e1 e2 ->
    (match hBSe' with
    | BSApp _ _ _ v1 v2 hBS1 hBS2 ->
      let hBS1' = lemma_bigstep_substitute_intros i rows e vs e1 v1 hBSse hBS1 in
      let hBS2' = lemma_bigstep_substitute_intros i rows e vs e2 v2 hBSse hBS2 in
      assert_norm (subst1' (XApp e1 e2) i e == XApp (subst1' e1 i e) (subst1' e2 i e));
      BSApp _ _ _ v1 v2 hBS1' hBS2')
  | XFby v0 e1 ->
    (match hBSe' with
    | BSFby1 _ _ _ -> BSFby1 [row] v0 (subst1' e1 i e)
    | BSFbyS _ _ _ _ _ hBS1 ->
      let BSsS prefix _ vs' _ _ hBSse' _ = hBSse in
      let hBS1' = lemma_bigstep_substitute_intros i prefix e vs' e1 a hBSse' hBS1 in
      BSFbyS row rows' v0 a _ hBS1')
  | XThen e1 e2 ->
    (match hBSe' with
    | BSThen1 _ _ _ v1 hBS1 ->
      let hBS1' = lemma_bigstep_substitute_intros i rows e vs e1 v1 hBSse hBS1 in
      BSThen1 _ (subst1' e1 i e) (subst1' e2 i e) v1 hBS1'
    | BSThenS _ _ _ v2 hBS2 ->
      let hBS2' = lemma_bigstep_substitute_intros i rows e vs e2 v2 hBSse hBS2 in
      BSThenS _ (subst1' e1 i e) (subst1' e2 i e) v2 hBS2')
  | XMu _ e1 ->
    (match hBSe' with
    | BSMu inhabited _ _ _ hBSe1 ->
      let hBSX = lemma_bigstep_substitute_intros i rows e vs (subst1 e1 (XMu e1)) a hBSse hBSe1 in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert_norm (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) (lift1 e 'a)));
      BSMu inhabited _ (subst1' e1 (i + 1) (lift1 e 'a)) _ hBSX)
  | XCheck p e1 e2 ->
    (match hBSe' with
    | BSCheck _ _ _ _ _ hBS2 ->
      let hBS2' = lemma_bigstep_substitute_intros i rows e vs e2 a hBSse hBS2 in
      BSCheck _ p (subst1' e1 i e) (subst1' e2 i e) _ hBS2')
  | XLet b e1 e2 ->
    (match hBSe' with
    | BSLet _ _ _ _ hBSX ->
      let hBSX' = lemma_bigstep_substitute_intros i rows e vs (subst1 e2 e1) a hBSse hBSX in
      lemma_subst_subst_distribute_le e2 0 i e1 e;
      assert_norm (subst1' (XLet b e1 e2) i e == XLet b (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)));
      BSLet _ (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)) _ hBSX')

#push-options "--fuel 1 --ifuel 0"

let lemma_bigstep_substitute_intros_no_dep_XApp
  (i: C.index { i < List.Tot.length 'c })
  (rows: list (C.row (C.drop1 'c i)))
  (e: exp (C.drop1 'c i) (C.get_index 'c i))
  (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
  (e1': exp 'c ('b -> 'a))
  (e2': exp 'c 'b)
  (r: C.row (C.drop1 'c i))
  (v: C.get_index 'c i)
  (vf: ('b -> 'a))
  (vb: 'b)
  (hBSse: bigsteps rows e vs)
  (hBS1': bigstep (r :: rows) (subst1' e1' i e) vf)
  (hBS2': bigstep (r :: rows) (subst1' e2' i e) vb):
    Tot (bigstep (r :: rows) (subst1' (XApp e1' e2') i e) (vf vb)) =
      assert_norm (subst1' (XApp e1' e2') i e == XApp (subst1' e1' i e) (subst1' e2' i e));
      BSApp _ _ _ vf vb hBS1' hBS2'

let lemma_bigstep_substitute_intros_no_dep_XMu
  {| Pipit.Inhabited.inhabited 'a |}
  (i: C.index { i < List.Tot.length 'c })
  (rows: list (C.row (C.drop1 'c i)))
  (e: exp (C.drop1 'c i) (C.get_index 'c i))
  (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
  (e1': exp ('a :: 'c) 'a)
  (r: C.row (C.drop1 'c i))
  (v: C.get_index 'c i)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBS1': bigstep (r :: rows) (subst1' (subst1 e1' (XMu e1')) i e) a):
    Tot (bigstep (r :: rows) (subst1' (XMu e1') i e) a) =
      lemma_subst_subst_distribute_XMu e1' i e;
      assert_norm (subst1' (XMu e1') i e == XMu (subst1' e1' (i + 1) (lift1 e 'a)));
      BSMu _ _ (subst1' e1' (i + 1) (lift1 e 'a)) _ hBS1'

let lemma_bigstep_substitute_intros_no_dep_XLet
  (i: C.index { i < List.Tot.length 'c })
  (rows: list (C.row (C.drop1 'c i)))
  (e: exp (C.drop1 'c i) (C.get_index 'c i))
  (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
  (e1': exp 'c 'b)
  (e2': exp ('b :: 'c) 'a)
  (r: C.row (C.drop1 'c i))
  (v: C.get_index 'c i)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBSX': bigstep (r :: rows) (subst1' (subst1 e2' e1') i e) a):
    Tot (bigstep (r :: rows) (subst1' (XLet 'b e1' e2') i e) a) =
      lemma_subst_subst_distribute_le e2' 0 i e1' e;
      assert_norm (subst1' (XLet 'b e1' e2') i e == XLet 'b (subst1' e1' i e) (subst1' e2' (i + 1) (lift1 e 'b)));
      BSLet _ (subst1' e1' i e) (subst1' e2' (i + 1) (lift1 e 'b)) _ hBSX'

#pop-options

(* used indirectly by lemma_bigstep_total *)
let rec lemma_bigstep_substitute_intros_no_dep
  (i: C.index { i < List.Tot.length 'c })
  (rows: list (C.row (C.drop1 'c i)))
  (e: exp (C.drop1 'c i) (C.get_index 'c i))
  (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp 'c 'a { ~ (direct_dependency e' i) })
  (r: C.row (C.drop1 'c i))
  (v: C.get_index 'c i)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep (C.row_lift1_dropped i r v :: C.row_zip2_lift1_dropped i rows vs) e' a):
    Tot (bigstep (r :: rows) (subst1' e' i e) a) (decreases hBSe') =
  match e' with
  | XVal _ -> BSVal _ _
  | XVar _ -> false_elim ()
  | XBVar i' ->
    assert (i <> i');
    if i' < i
    then BSVar r rows i'
    else (
      C.lemma_drop_get_index_gt 'c i (i' - 1);
      assert (C.opt_index (C.drop1 'c i) (i' - 1) == Some 'a);
      assert_norm (subst1' (XBVar i') i e == XBVar #(C.drop1 'c i) #('a) (i' - 1));
      BSVar r rows (i' - 1))
  | XApp e1 e2 ->
    (match hBSe' with
    | BSApp _ _ _ v1 v2 hBS1 hBS2 ->
      assert_norm (direct_dependency (XApp e1 e2) i == (direct_dependency e1 i || direct_dependency e2 i));
      let hBS1' = lemma_bigstep_substitute_intros_no_dep i rows e vs e1 r v v1 hBSse hBS1 in
      let hBS2' = lemma_bigstep_substitute_intros_no_dep i rows e vs e2 r v v2 hBSse hBS2 in
      lemma_bigstep_substitute_intros_no_dep_XApp i rows e vs e1 e2 r v v1 v2 hBSse hBS1' hBS2')
  | XFby v0 e1 ->
    (match hBSe' with
    | BSFby1 _ _ _ -> BSFby1 [r] v0 (subst1' e1 i e)
    | BSFbyS _ _ _ _ _ hBS1 ->
      assert (Cons? rows);
      let hBS1' = lemma_bigstep_substitute_intros i rows e vs e1 a hBSse hBS1 in
      BSFbyS r rows v0 a (subst1' e1 i e) hBS1')
  | XThen e1 e2 ->
    (match hBSe' with
    | BSThen1 _ _ _ v1 hBS1 ->
      let hBS1' = lemma_bigstep_substitute_intros_no_dep i rows e vs e1 r v v1 hBSse hBS1 in
      BSThen1 _ (subst1' e1 i e) (subst1' e2 i e) v1 hBS1'
    | BSThenS _ _ _ v2 hBS2 ->
      let hBS2' = lemma_bigstep_substitute_intros_no_dep i rows e vs e2 r v v2 hBSse hBS2 in
      BSThenS _ (subst1' e1 i e) (subst1' e2 i e) v2 hBS2')
  | XMu _ e1 ->
    (match hBSe' with
    | BSMu inhabited _ _ _ hBSe1 ->
      lemma_direct_dependency_not_subst' i 0 e1 (XMu e1);
      C.lemma_dropCons 'a 'c (i + 1);
      C.lemma_get_index_Cons 'a 'c i;
      assert (C.drop1 ('a :: 'c) (i + 1) == 'a :: C.drop1 'c i);
      let hBSX = lemma_bigstep_substitute_intros_no_dep i rows e vs (subst1 e1 (XMu e1)) r v a hBSse hBSe1 in
      lemma_bigstep_substitute_intros_no_dep_XMu i rows e vs e1 r v a hBSse hBSX)
  | XCheck p e1 e2 ->
    (match hBSe' with
    | BSCheck _ _ _ _ _ hBS2 ->
      let hBS2' = lemma_bigstep_substitute_intros_no_dep i rows e vs e2 r v a hBSse hBS2 in
      BSCheck _ p (subst1' e1 i e) (subst1' e2 i e) _ hBS2')

  | XLet b e1 e2 ->
    (match hBSe' with
    | BSLet _ _ _ _ hBSX ->
      lemma_direct_dependency_not_subst' i 0 e2 e1;
      C.lemma_dropCons b 'c (i + 1);
      C.lemma_get_index_Cons b 'c i;
      assert (C.get_index (b :: 'c) (i + 1) == C.get_index 'c i);
      assert (C.drop1 (b :: 'c) (i + 1) == b :: C.drop1 'c i);
      let hBSX' = lemma_bigstep_substitute_intros_no_dep i rows e vs (subst1 e2 e1) r v a hBSse hBSX in
      lemma_bigstep_substitute_intros_no_dep_XLet i rows e vs e1 e2 r v a hBSse hBSX')

  | _ -> false_elim ()

(* used by transition system proof *)
let lemma_bigstep_substitute_elim_XLet
  (rows: list (C.row 'c) { Cons? rows })
  (e1: exp 'c 'b)
  (vs: list 'b { List.Tot.length rows == List.Tot.length vs })
  (hBS1s: bigsteps rows e1 vs)
  (e2: exp ('b :: 'c) 'a { causal e2 })
  (v: 'a)
  (hBS2: bigstep rows (XLet 'b e1 e2) v):
    (bigstep (C.row_zip2_cons vs rows) e2 v) =
  match hBS2 with
  | BSLet _ _ _ _ hBS2' ->
    lemma_bigstep_substitute_elim 0 rows e1 vs e2 v hBS1s hBS2'

(* used by transition system proof *)
let lemma_bigstep_substitute_elim_XMu
  {| Pipit.Inhabited.inhabited 'a |}
  (rows: list (C.row 'c) { Cons? rows })
  (e: exp ('a :: 'c) 'a { causal (XMu e) })
  (vs: list 'a { List.Tot.length rows == List.Tot.length vs })
  (hBSs: bigsteps rows (XMu e) vs):
    (bigstep (C.row_zip2_cons vs rows) e (List.Tot.hd vs)) =
    match hBSs with
    | BSsS _ _ _ _ _ _ hBS ->
      match hBS with
      | BSMu _ _ _ _ hBS' ->
        lemma_bigstep_substitute_elim 0 rows (XMu e) vs e (List.Tot.hd vs) hBSs hBS'

(* used by lemma_bigstep_total *)
let lemma_bigstep_substitute_intros_XMu
  {| Pipit.Inhabited.inhabited 'a |}
  (rows: list (C.row 'c))
  (e: exp ('a :: 'c) 'a { causal (XMu e) })
  (vs: list 'a { List.Tot.length rows == List.Tot.length vs })
  (row: C.row 'c)
  (v v': 'a)
  (hBSs: bigsteps rows (XMu e) vs)
  (hBS1: bigstep (C.row_cons v' row :: C.row_zip2_cons vs rows) e v):
    (bigstep (row :: rows) (XMu e) v) =
    let hBS'': bigstep (row :: rows) (subst1 e (XMu e)) v = lemma_bigstep_substitute_intros_no_dep 0 rows (XMu e) vs e row v' v hBSs hBS1 in
    BSMu _ (row :: rows) e v hBS''

(* used by transition system proof *)
let rec lemma_bigstep_total
  (rows: list (C.row 'c) { Cons? rows }) (e: exp 'c 'a { causal e }):
    Tot (v: 'a & bigstep rows e v) (decreases %[e; rows; 0]) =
  let hd = List.Tot.hd rows in
  let tl = List.Tot.tl rows in
  match e with
  | XVal v -> (| v, BSVal _ v |)
  | XVar _ -> false_elim ()
  | XBVar i ->
    (| C.row_index 'c hd i, BSVar hd tl i |)
  | XApp f_e a_e ->
    assert_norm (causal (XApp f_e a_e) == (causal f_e && causal a_e));
    let (| f_v, hBSf |) = lemma_bigstep_total rows f_e in
    let (| a_v, hBSa |) = lemma_bigstep_total rows a_e in
    (| f_v a_v, BSApp _ _ _ _ _ hBSf hBSa |)
  | XFby v0 e1 ->
    (match rows with
    | [_] ->
      assert_norm (List.Tot.length rows == 1);
      (| v0, BSFby1 rows v0 e1 |)
    | latest :: prefix ->
      let (| v', hBSe1 |) = lemma_bigstep_total prefix e1 in
      (| v', BSFbyS latest prefix v0 v' e1 hBSe1 |))
  | XThen e1 e2 ->
    (match rows with
    | [_] ->
      assert_norm (List.Tot.length rows == 1);
      let (| v1, hBS1 |) = lemma_bigstep_total rows e1 in
      (| v1, BSThen1 rows e1 e2 v1 hBS1 |)
    | _ ->
      assert_norm (List.Tot.length rows > 1);
      let (| v2, hBS2 |) = lemma_bigstep_total rows e2 in
      (| v2, BSThenS rows e1 e2 v2 hBS2 |))

  | XMu _ e1 ->
    let (| vs, hBSs |) = lemma_bigsteps_total tl e in
    let v' = Pipit.Inhabited.get_inhabited in
    let (| v, hBS0 |) = lemma_bigstep_total (C.row_cons v' hd :: C.row_zip2_cons vs tl) e1 in
    let hBS' = lemma_bigstep_substitute_intros_XMu tl e1 vs hd v v' hBSs hBS0 in
    (| v, hBS' |)

  | XCheck p e1 e2 ->
    let (| v2, hBS2 |) = lemma_bigstep_total rows e2 in
    (| v2, BSCheck rows p e1 e2 v2 hBS2 |)

  | XLet b e1 e2 ->
    let (| vs, hBSs |) = lemma_bigsteps_total rows e1 in
    let (| v, hBS2 |) = lemma_bigstep_total (C.row_zip2_cons vs rows) e2 in
    let hBS' = lemma_bigstep_substitute_intros 0 rows e1 vs e2 v hBSs hBS2 in
    (| v, BSLet rows e1 e2 v hBS' |)

and lemma_bigsteps_total
  (rows: list (C.row 'c)) (e: exp 'c 'a { causal e }):
    Tot (vs: list 'a { List.Tot.length vs == List.Tot.length rows } & bigsteps rows e vs) (decreases %[e; rows; 1]) =
  match rows with
  | [] -> (| [], BSs0 e |)
  | r :: rows' ->
    let (| vs, hBSs |) = lemma_bigsteps_total rows' e in
    let (| v,  hBS1 |) = lemma_bigstep_total  rows  e in
    (| v :: vs, BSsS _ _ _ r v hBSs hBS1 |)

let lemma_bigstep_total_v
  (rows: list (C.row 'c) { Cons? rows }) (e: exp 'c 'a { causal e }):
    'a =
  let (| v, _ |) = lemma_bigstep_total rows e in
  v
