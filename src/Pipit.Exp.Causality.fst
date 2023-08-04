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
let direct_dependency_base (#t: table) (#c: context t) (#a: t.ty) (e: exp_base t c a) (i: C.index) : Tot bool (decreases e) =
  match e with
  | XVal _ -> false
  | XVar _ -> false
  | XBVar i' -> i = i'

(* Direct dependencies: does expression `e` have a non-delayed dependency on bound-variable `i`?
    *)
let rec direct_dependency (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a) (i: C.index) : Tot bool (decreases e) =
  match e with
  | XBase b -> direct_dependency_base b i
  | XApps e1 -> direct_dependency_apps e1 i
  | XFby _ _ -> false
  | XMu e1 -> direct_dependency e1 (i + 1)
  (* This is more restrictive than necessary. The following should work:
     > rec x. let y = x + 1 in 0 fby y
     Maybe the definition should allow `e1` to directly refer to `i` if `e2` does
     not directly refer to `e1`:
     > XLet b e1 e2 ->
     >    (if direct_dependency e1 i then direct_dependency e2 0 else false) ||
     >        direct_dependency e2 (i + 1)
  *)
  | XLet b e1 e2 -> direct_dependency e1 i || direct_dependency e2 (i + 1)
  | XCheck name e1 -> direct_dependency e1 i
  (* Should we care if a contract's relies or guarantees mention `i`?
     I don't think so - causality is required for total evaluation, which
     uses the implementation rather than the abstraction. *)
  | XContract rely guar impl -> direct_dependency impl i

and direct_dependency_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a) (i: C.index) : Tot bool (decreases e) =
  match e with
  | XPrim _ -> false
  | XApp e1 e2 -> direct_dependency_apps e1 i || direct_dependency e2 i

(* Causality: are all references to recursive streams delayed?
   All causal expressions make progress.
   We also sneak in a well-formedness check here that there are no free
   variables. This is really a different check, but it's convenient.
*)
let causal_base (#t: table) (#c: context t) (#a: t.ty) (e: exp_base t c a): Tot bool =
  match e with
  | XVal _ -> true
  | XVar _ -> false // no free variables
  | XBVar _ -> true

let rec causal (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot bool (decreases e) =
  match e with
  | XBase e1 -> causal_base e1
  | XApps e1 -> causal_apps e1
  | XFby _ e1 -> causal e1
  | XMu e1 -> causal e1 && not (direct_dependency e1 0)
  | XLet b e1 e2 -> causal e1 && causal e2
  | XCheck _ e1 -> causal e1
  | XContract rely guar impl -> causal impl

and causal_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot bool (decreases e) =
  match e with
  | XPrim _ -> true
  | XApp e1 e2 -> causal_apps e1 && causal e2

#push-options "--fuel 1 --ifuel 1"

#push-options "--split_queries always"

(*

(* used by lemma_direct_dependency_not_subst', lemma_direct_dependency_not_subst' needs i' < i case *)
let rec lemma_direct_dependency_lift_ge (#tbl: table) (#c: context tbl) (e: exp tbl c 'a) (i: C.index_lookup c) (i': C.index { i >= i' /\ i' <= List.Tot.length c }) (t: tbl.ty):
    Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) (i + 1)) (decreases e) =
  match e with
  | XVal _ | XVar _ | XBVar _ | XPrim _ -> ()
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
  | XMu e1 ->
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
let rec lemma_direct_dependency_not_subst'
  (#tbl: table) (#c: context tbl)
  (i: C.index) (i': C.index { C.has_index c i' /\ i' <= i })
  (e: exp tbl c 'a { ~ (direct_dependency e (i + 1)) })
  (p: val_exp tbl (C.drop1 c i') (C.get_index c i') { ~ (direct_dependency p i ) }):
    Lemma
      (requires (C.has_index (C.drop1 c i') i))
      (ensures ~ (direct_dependency (subst1' e i' p) i)) (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar _ -> ()
  | XPrim _ -> ()
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
  | XMu e1 ->
    lemma_direct_dependency_lift_ge p i 0 (XMu?.valty e);
    lemma_direct_dependency_not_subst' (i + 1) (i' + 1) e1 (lift1 p (XMu?.valty e))
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
  (#t: table)
  (#c: context t)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: val_exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp t c 'a)
  (v': 'a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep rows (subst1' e' i e) v'):
    Tot (bigstep (CP.row_zip2_lift1_dropped i rows vs) e' v') (decreases hBSe') =
  let latest = List.Tot.hd rows in
  let rows' = CP.row_zip2_lift1_dropped i rows vs in
  let latest' = List.Tot.hd rows' in
  match e' with
  | XVal v -> BSVal _ v
  | XVar _ -> false_elim ()
  | XPrim p -> BSPrim _ p
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
  | XMu e1 ->
    (match hBSe' with
    | BSMu _ e1' _ hBSe1 ->
      let valty = XMu?.valty e' in
      CP.lemma_dropCons valty c (i + 1);
      assert (C.drop1 (valty :: c) (i + 1) == valty :: C.drop1 c i);
      let lifted: val_exp t (C.drop1 (valty :: c) (i + 1)) (C.get_index (valty :: c) (i + 1)) = lift1 e valty in
      assert_norm (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) lifted));

      let se: val_exp t (valty :: C.drop1 c i) valty = e1' in
      let se: val_exp t (C.drop1 c i) valty = subst1 e1' (XMu e1') in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert (subst1 (subst1' e1 (i + 1) lifted) (XMu e1') == subst1' (subst1 e1 (XMu e1)) i e);
      let hBSe1': bigstep rows se v' = hBSe1 in
      let hBSX = lemma_bigstep_substitute_elim i rows e vs (subst1 e1 (XMu e1)) v' hBSse hBSe1' in
      BSMu _ e1 _ hBSX)
  | XLet b e1 e2 ->
    (match hBSe' with
    | BSLet _ e1' e2' _ hBSe1' ->
      CP.lemma_dropCons b c (i + 1);
      assert (C.drop1 (b :: c) (i + 1) == b :: C.drop1 c i);
      CP.lemma_get_index_Cons b c i;
      let lifted: val_exp t (C.drop1 (b :: c) (i + 1)) (C.get_index (b :: c) (i + 1)) = lift1 e b in
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
  (#t: table)
  (#c: context t)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: val_exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp t c 'a)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep (CP.row_zip2_lift1_dropped i rows vs) e' a):
    Tot (bigstep rows (subst1' e' i e) a) (decreases hBSe') =
  let row = List.Tot.hd rows in
  let rows' = List.Tot.tl rows in
  match e' with
  | XVal v -> BSVal rows v
  | XPrim p -> BSPrim rows p
  | XVar _ -> false_elim ()
  | XBVar i' ->
    if i = i'
    then (let BSsS _ _ _ _ _ _ hBSe = hBSse in hBSe)
    else if i' < i
    then BSVar row rows' i'
    else (
      CP.lemma_drop_get_index_gt c i (i' - 1);
      assert (C.opt_index (C.drop1 c i) (i' - 1) == Some (C.get_index c i'));
      assert_norm (subst1' (XBVar i') i e == XBVar #t #(C.drop1 c i) (i' - 1));
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
  | XMu e1 ->
    (match hBSe' with
    | BSMu _ _ _ hBSe1 ->
      let valty = XMu?.valty e' in
      let hBSX = lemma_bigstep_substitute_intros i rows e vs (subst1 e1 (XMu e1)) a hBSse hBSe1 in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) (lift1 e valty)));
      BSMu _ (subst1' e1 (i + 1) (lift1 e valty)) _ hBSX)
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
  (#t: table)
  (#c: context t)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: val_exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e1': exp t c ('b -> 'a))
  (e2': exp t c 'b)
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (vf: ('b -> 'a))
  (vb: 'b)
  (hBSse: bigsteps rows e vs)
  (hBS1': bigstep (r :: rows) (subst1' e1' i e) vf)
  (hBS2': bigstep (r :: rows) (subst1' e2' i e) vb):
    Tot (bigstep (r :: rows) (subst1' (XApp e1' e2') i e) (vf vb)) =
      assert_norm (subst1' (XApp e1' e2') i e == XApp (subst1' e1' i e) (subst1' e2' i e));
      BSApp _ _ _ vf vb hBS1' hBS2'

let lemma_bigstep_substitute_intros_no_dep_XMu
  (#t: table)
  (#c: context t)
  (#valty: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: val_exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e1': val_exp t (valty :: c) valty)
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (a: t.ty_sem valty)
  (hBSse: bigsteps rows e vs)
  (hBS1': bigstep (r :: rows) (subst1' (subst1 e1' (XMu e1')) i e) a):
    Tot (bigstep (r :: rows) (subst1' (XMu e1') i e) a) =
      lemma_subst_subst_distribute_XMu e1' i e;
      assert_norm (subst1' (XMu e1') i e == XMu (subst1' e1' (i + 1) (lift1 e valty)));
      BSMu _ (subst1' e1' (i + 1) (lift1 e valty)) _ hBS1'

let lemma_bigstep_substitute_intros_no_dep_XLet
  (#t: table)
  (#c: context t)
  (#valty: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: val_exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e1': val_exp t c valty)
  (e2': exp t (valty :: c) 'a)
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBSX': bigstep (r :: rows) (subst1' (subst1 e2' e1') i e) a):
    Tot (bigstep (r :: rows) (subst1' (XLet valty e1' e2') i e) a) =
      lemma_subst_subst_distribute_le e2' 0 i e1' e;
      assert_norm (subst1' (XLet valty e1' e2') i e == XLet valty (subst1' e1' i e) (subst1' e2' (i + 1) (lift1 e valty)));
      BSLet _ (subst1' e1' i e) (subst1' e2' (i + 1) (lift1 e valty)) _ hBSX'

#pop-options

(* used indirectly by lemma_bigstep_total *)
let rec lemma_bigstep_substitute_intros_no_dep
  (#t: table)
  (#c: context t)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: val_exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp t c 'a { ~ (direct_dependency e' i) })
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (a: 'a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep (CP.row_lift1_dropped i r v :: CP.row_zip2_lift1_dropped i rows vs) e' a):
    Tot (bigstep (r :: rows) (subst1' e' i e) a) (decreases hBSe') =
  match e' with
  | XVal v -> BSVal _ v
  | XPrim p -> BSPrim _ p
  | XVar _ -> false_elim ()
  | XBVar i' ->
    assert (i <> i');
    if i' < i
    then BSVar r rows i'
    else (
      CP.lemma_drop_get_index_gt c i (i' - 1);
      assert (C.opt_index (C.drop1 c i) (i' - 1) == Some (C.get_index c i'));
      assert_norm (subst1' (XBVar i') i e == XBVar #t #(C.drop1 c i) (i' - 1));
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
  | XMu e1 ->
    (match hBSe' with
    | BSMu _ _ _ hBSe1 ->
      let valty = XMu?.valty e' in
      lemma_direct_dependency_not_subst' i 0 e1 (XMu e1);
      CP.lemma_dropCons valty c (i + 1);
      CP.lemma_get_index_Cons valty c i;
      assert (C.drop1 (valty :: c) (i + 1) == valty :: C.drop1 c i);
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
      CP.lemma_dropCons b c (i + 1);
      CP.lemma_get_index_Cons b c i;
      assert (C.get_index (b :: c) (i + 1) == C.get_index c i);
      assert (C.drop1 (b :: c) (i + 1) == b :: C.drop1 c i);
      let hBSX' = lemma_bigstep_substitute_intros_no_dep i rows e vs (subst1 e2 e1) r v a hBSse hBSX in
      lemma_bigstep_substitute_intros_no_dep_XLet i rows e vs e1 e2 r v a hBSse hBSX')

  | _ -> false_elim ()

*)

(* used by transition system proof *)
let lemma_bigstep_substitute_elim_XLet
  (#t: table)
  (#c: context t)
  (#valty #a: t.ty)
  (rows: list (row c) { Cons? rows })
  (e1: exp t c valty)
  (vs: list (t.ty_sem valty) { List.Tot.length rows == List.Tot.length vs })
  (hBS1s: bigsteps rows e1 vs)
  (e2: exp t (valty :: c) a { causal e2 })
  (v: t.ty_sem a)
  (hBS2: bigstep rows (XLet valty e1 e2) v):
    (bigstep (CR.zip2_cons vs rows) e2 v) =
  match hBS2 with
  | BSLet _ _ _ _ hBS2' ->
    admit () // lemma_bigstep_substitute_elim 0 rows e1 vs e2 v hBS1s hBS2'

(* used by transition system proof *)
let lemma_bigstep_substitute_elim_XMu
  (#t: table)
  (#c: context t)
  (#valty: t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp t (valty :: c) valty { causal (XMu e) })
  (vs: list (t.ty_sem valty) { List.Tot.length rows == List.Tot.length vs })
  (hBSs: bigsteps rows (XMu e) vs):
    (bigstep (CR.zip2_cons vs rows) e (List.Tot.hd vs)) =
    match hBSs with
    | BSsS _ _ _ _ _ _ hBS ->
      match hBS with
      | BSMu _ _ _ hBS' ->
        admit () // lemma_bigstep_substitute_elim 0 rows (XMu e) vs e (List.Tot.hd vs) hBSs hBS'

(* used by lemma_bigstep_total *)
let lemma_bigstep_substitute_intros_XMu
  (#t: table)
  (#c: context t)
  (#valty: t.ty)
  (rows: list (row c))
  (e: exp t (valty :: c) valty { causal (XMu e) })
  (vs: list (t.ty_sem valty) { List.Tot.length rows == List.Tot.length vs })
  (row: row c)
  (v v': t.ty_sem valty)
  (hBSs: bigsteps rows (XMu e) vs)
  (hBS1: bigstep (CR.cons v' row :: CR.zip2_cons vs rows) e v):
    (bigstep (row :: rows) (XMu e) v) =
    let hBS'': bigstep (row :: rows) (subst1 e (XMu e)) v =
      // lemma_bigstep_substitute_intros_no_dep 0 rows (XMu e) vs e row v' v hBSs hBS1 in
      admit () in
    BSMu (row :: rows) e v hBS''

(* used by transition system proof *)
let rec lemma_bigstep_total
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp t c a { causal e }):
    Tot (v: t.ty_sem a & bigstep rows e v) (decreases %[e; rows; 0]) =
  let hd = List.Tot.hd rows in
  let tl = List.Tot.tl rows in
  admit ()
  // match e with
  // | XVal v -> (| v, BSVal _ v |)
  // | XPrim p -> (| t.prim_sem p, BSPrim rows p |)
  // | XVar _ -> false_elim ()
  // | XBVar i ->
  //   (| CR.index (context_sem c) hd i, BSVar hd tl i |)
  // | XApp f_e a_e ->
  //   assert_norm (causal (XApp f_e a_e) == (causal f_e && causal a_e));
  //   let (| f_v, hBSf |) = lemma_bigstep_total rows f_e in
  //   let (| a_v, hBSa |) = lemma_bigstep_total rows a_e in
  //   (| f_v a_v, BSApp _ _ _ _ _ hBSf hBSa |)
  // | XFby v0 e1 ->
  //   (match rows with
  //   | [_] ->
  //     assert_norm (List.Tot.length rows == 1);
  //     (| v0, BSFby1 rows v0 e1 |)
  //   | latest :: prefix ->
  //     let (| v', hBSe1 |) = lemma_bigstep_total prefix e1 in
  //     (| v', BSFbyS latest prefix v0 v' e1 hBSe1 |))
  // | XMu e1 ->
  //   let (| vs, hBSs |) = lemma_bigsteps_total tl e in
  //   let v' = t.val_default (XMu?.valty e) in
  //   let (| v, hBS0 |) = lemma_bigstep_total (CR.cons v' hd :: CR.zip2_cons vs tl) e1 in
  //   let hBS' = lemma_bigstep_substitute_intros_XMu tl e1 vs hd v v' hBSs hBS0 in
  //   (| v, hBS' |)

  // | XCheck p e1 e2 ->
  //   let (| v2, hBS2 |) = lemma_bigstep_total rows e2 in
  //   (| v2, BSCheck rows p e1 e2 v2 hBS2 |)

  // | XLet b e1 e2 ->
  //   let (| vs, hBSs |) = lemma_bigsteps_total rows e1 in
  //   let (| v, hBS2 |) = lemma_bigstep_total (CR.zip2_cons vs rows) e2 in
  //   let hBS' = admit () in // lemma_bigstep_substitute_intros 0 rows e1 vs e2 v hBSs hBS2 in
  //   (| v, BSLet rows e1 e2 v hBS' |)

and lemma_bigsteps_total
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c)) (e: exp t c a { causal e }):
    Tot (vs: list (t.ty_sem a) { List.Tot.length vs == List.Tot.length rows } & bigsteps rows e vs) (decreases %[e; rows; 1]) =
  match rows with
  | [] -> (| [], BSs0 e |)
  | r :: rows' ->
    let (| vs, hBSs |) = lemma_bigsteps_total rows' e in
    let (| v,  hBS1 |) = lemma_bigstep_total  rows  e in
    (| v :: vs, BSsS _ _ _ r v hBSs hBS1 |)

let lemma_bigstep_total_v
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c) { Cons? rows }) (e: exp t c a { causal e }):
    t.ty_sem a =
  let (| v, _ |) = lemma_bigstep_total rows e in
  v
