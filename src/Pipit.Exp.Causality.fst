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
     I don't think it's strictly necessary - causality is required for total evaluation, which
     uses the implementation rather than the abstraction. *)
  | XContract _ rely guar impl ->
    direct_dependency rely i ||
    direct_dependency guar (i + 1) ||
    direct_dependency impl i

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
  | XContract _ rely guar impl ->
    causal rely && causal guar && causal impl

and causal_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot bool (decreases e) =
  match e with
  | XPrim _ -> true
  | XApp e1 e2 -> causal_apps e1 && causal e2

(* used by lemma_direct_dependency_not_subst', lemma_direct_dependency_not_subst' needs i' < i case *)
let rec lemma_direct_dependency_lift_ge (#tbl: table) (#c: context tbl) (#a: tbl.ty) (e: exp tbl c a) (i: C.index_lookup c) (i': C.index { i >= i' /\ i' <= List.Tot.length c }) (t: tbl.ty):
    Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) (i + 1)) (decreases e) =
  match e with
  | XBase _ -> ()
  | XApps e1 -> lemma_direct_dependency_lift_ge_apps e1 i i' t
  | XFby _ e1 -> lemma_direct_dependency_lift_ge e1 i i' t
  | XMu e1 -> lemma_direct_dependency_lift_ge e1 (i + 1) (i' + 1) t
  | XLet b e1 e2 ->
    lemma_direct_dependency_lift_ge e1 i i' t;
    lemma_direct_dependency_lift_ge e2 (i + 1) (i' + 1) t
  | XCheck _ e1 ->
    lemma_direct_dependency_lift_ge e1 i i' t
  | XContract _ rely guar impl ->
    lemma_direct_dependency_lift_ge rely i i' t;
    lemma_direct_dependency_lift_ge guar (i + 1) (i' + 1) t;
    lemma_direct_dependency_lift_ge impl i i' t
and
  lemma_direct_dependency_lift_ge_apps (#tbl: table) (#c: context tbl) (#a: funty tbl.ty) (e: exp_apps tbl c a) (i: C.index_lookup c) (i': C.index { i >= i' /\ i' <= List.Tot.length c }) (t: tbl.ty):
      Lemma (ensures direct_dependency_apps e i == direct_dependency_apps (lift1_apps' e i' t) (i + 1)) (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp ea e ->
    lemma_direct_dependency_lift_ge_apps ea i i' t;
    lemma_direct_dependency_lift_ge e i i' t

// let rec lemma_direct_dependency_lift_lt (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) (i': C.index { i < i' /\ i' <= List.Tot.length 'c }) (t: Type):
//     Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) i) (decreases e) =

(* used by lemma_bigstep_substitute_intros_no_dep *)
let rec lemma_direct_dependency_not_subst
  (#tbl: table) (#c: context tbl) (#a: tbl.ty)
  (i: C.index) (i': C.index { C.has_index c i' /\ i' <= i })
  (e: exp tbl c a { ~ (direct_dependency e (i + 1)) })
  (p: exp tbl (C.drop1 c i') (C.get_index c i') { ~ (direct_dependency p i ) }):
    Lemma
      (requires (C.has_index (C.drop1 c i') i))
      (ensures ~ (direct_dependency (subst1' e i' p) i)) (decreases e) =
  match e with
  | XBase _ -> ()
  | XApps ea -> lemma_direct_dependency_not_subst_apps i i' ea p
  | XFby v1 e2 ->
    ()
  | XMu e1 ->
    lemma_direct_dependency_lift_ge p i 0 (XMu?.valty e);
    lemma_direct_dependency_not_subst (i + 1) (i' + 1) e1 (lift1 p (XMu?.valty e))
  | XLet b e1 e2 ->
    lemma_direct_dependency_not_subst i i' e1 p;
    lemma_direct_dependency_lift_ge p i 0 b;
    lemma_direct_dependency_not_subst (i + 1) (i' + 1) e2 (lift1 p b)
  | XCheck _ e1 ->
    lemma_direct_dependency_not_subst i i' e1 p
  | XContract _ rely guar body ->
    lemma_direct_dependency_not_subst i i' rely p;
    lemma_direct_dependency_lift_ge p i 0 a;
    lemma_direct_dependency_not_subst (i + 1) (i' + 1) guar (lift1 p a);
    lemma_direct_dependency_not_subst i i' body p

and lemma_direct_dependency_not_subst_apps
  (#tbl: table) (#c: context tbl) (#a: funty tbl.ty)
  (i: C.index) (i': C.index { C.has_index c i' /\ i' <= i })
  (e: exp_apps tbl c a { ~ (direct_dependency_apps e (i + 1)) })
  (p: exp tbl (C.drop1 c i') (C.get_index c i') { ~ (direct_dependency p i ) }):
    Lemma
      (requires (C.has_index (C.drop1 c i') i))
      (ensures ~ (direct_dependency_apps (subst1_apps' e i' p) i)) (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp ea e ->
    lemma_direct_dependency_not_subst_apps i i' ea p;
    lemma_direct_dependency_not_subst i i' e p

(* used by lemma_bigstep_substitute_elim_XMu, indirectly by transition system proof *)
let lemma_bigstep_substitute_elim_base
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp_base t c a)
  (v': t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep rows (subst1_base' e' i e) v'):
    Tot (bigstep_base (CP.row_zip2_lift1_dropped i rows vs) e' v') =
  let rows' = CP.row_zip2_lift1_dropped i rows vs in
  let latest' = List.Tot.hd rows' in
  match e' with
  | XVal v -> BSVal _ v
  | XVar x -> false_elim ()
  | XBVar i' ->
    if i = i'
    then
      (match hBSse with
        | BSsS r e_ _ _ v hBSsep hBSe ->
          bigstep_deterministic hBSe hBSe';
          BSVar latest' (List.Tot.tl rows') i)
    else
      (match hBSe' with
       | BSBase _ _ _ (BSVar _latest _prefix ix_drop) ->
         BSVar latest' (List.Tot.tl rows') i')

#push-options "--split_queries always"

let rec lemma_bigstep_substitute_elim
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp t c a)
  (v': t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep rows (subst1' e' i e) v'):
    Tot (bigstep (CP.row_zip2_lift1_dropped i rows vs) e' v') (decreases hBSe') =
  let latest = List.Tot.hd rows in
  let rows' = CP.row_zip2_lift1_dropped i rows vs in
  let latest' = List.Tot.hd rows' in
  match e' with
  | XBase e' ->
    BSBase _ _ _ (lemma_bigstep_substitute_elim_base i rows e vs e' v' hBSse hBSe')
  | XApps ea ->
    (match hBSe' with
    | BSApps _ _ _ hBSea' ->
      BSApps _ _ _ (lemma_bigstep_substitute_elim_apps i rows e vs ea v' hBSse hBSea'))
  | XFby v1 e2 ->
    (match hBSe' with
    | BSFby1 _ _ _ -> BSFby1 _ v1 e2
    | BSFbyS latest prefix _ v2 _ hBS2 ->
      let BSsS _ _ vs' _ _ hBSse' _ = hBSse in
      let hBS2' = lemma_bigstep_substitute_elim i prefix e vs' e2 v2 hBSse' hBS2 in
      BSFbyS latest' (List.Tot.tl rows') v1 v2 e2 hBS2')
  | XMu e1 ->
    (match hBSe' with
    | BSMu _ e1' _ hBSe1 ->
      let valty = XMu?.valty e' in
      CP.lemma_dropCons valty c (i + 1);
      assert (C.drop1 (valty :: c) (i + 1) == valty :: C.drop1 c i);
      let lifted: exp t (C.drop1 (valty :: c) (i + 1)) (C.get_index (valty :: c) (i + 1)) = lift1 e valty in
      assert_norm (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) lifted));

      let se: exp t (valty :: C.drop1 c i) valty = e1' in
      let se: exp t (C.drop1 c i) valty = subst1 e1' (XMu e1') in
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
      let lifted: exp t (C.drop1 (b :: c) (i + 1)) (C.get_index (b :: c) (i + 1)) = lift1 e b in
      assert_norm (subst1' (XLet b e1 e2) i e == XLet b (subst1' e1 i e) (subst1' e2 (i + 1) lifted));

      lemma_subst_subst_distribute_le e2 0 i e1 e;
      let hBSX = lemma_bigstep_substitute_elim i rows e vs (subst1 e2 e1) v' hBSse hBSe1' in
      BSLet _ e1 e2 _ hBSX)
  | XCheck p e1 ->
    (match hBSe' with
    | BSCheck _ _ _ v'' hBS1 ->
      let hBS1' = lemma_bigstep_substitute_elim i rows e vs e1 v'' hBSse hBS1 in
      BSCheck _ p e1 _ hBS1')
  | XContract ps r g e1 ->
    (match hBSe' with
    | BSContract _ _ _ _ _ v'' hBS1 ->
      let hBS1' = lemma_bigstep_substitute_elim i rows e vs e1 v'' hBSse hBS1 in
      BSContract _ ps r g _ v'' hBS1')
and lemma_bigstep_substitute_elim_apps
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp_apps t c a)
  (v': funty_sem t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep_apps rows (subst1_apps' e' i e) v'):
    Tot (bigstep_apps (CP.row_zip2_lift1_dropped i rows vs) e' v') (decreases hBSe') =
  match e' with
  | XPrim p -> BSPrim _ p
  | XApp e1 e2 ->
    (match hBSe' with
    | BSApp _ _ _ v1 v2 hBS1 hBS2 ->
      assert_norm (subst1_apps' (XApp e1 e2) i e == XApp (subst1_apps' e1 i e) (subst1' e2 i e));
      let hBS1' = lemma_bigstep_substitute_elim_apps i rows e vs e1 v1 hBSse hBS1 in
      let hBS2' = lemma_bigstep_substitute_elim i rows e vs e2 v2 hBSse hBS2 in
      BSApp _ _ _ v1 v2 hBS1' hBS2')

(* used by lemma_bigstep_substitute_intros_no_dep, indirectly by lemma_bigstep_total *)
let lemma_bigstep_substitute_intros_base
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp_base t c a)
  (v: t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep_base (CP.row_zip2_lift1_dropped i rows vs) e' v):
    Tot (bigstep rows (subst1_base' e' i e) v) (decreases hBSe') =
  let row = List.Tot.hd rows in
  let rows' = List.Tot.tl rows in
  match e' with
  | XVal v -> BSBase _ _ _ (BSVal rows v)
  | XVar _ -> false_elim ()
  | XBVar i' ->
    if i = i'
    then (let BSsS _ _ _ _ _ _ hBSe = hBSse in hBSe)
    else if i' < i
    then BSBase _ _ _ (BSVar row rows' i')
    else (
      CP.lemma_drop_get_index_gt c i (i' - 1);
      assert (C.opt_index (C.drop1 c i) (i' - 1) == Some (C.get_index c i'));
      assert_norm (subst1_base' (XBVar i') i e == XBase (XBVar #t #(C.drop1 c i) (i' - 1)));
      BSBase _ _ _ (BSVar row rows' (i' - 1)))

let rec lemma_bigstep_substitute_intros
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp t c a)
  (v: t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep (CP.row_zip2_lift1_dropped i rows vs) e' v):
    Tot (bigstep rows (subst1' e' i e) v) (decreases hBSe') =
  let row = List.Tot.hd rows in
  let rows' = List.Tot.tl rows in
  match e' with
  | XBase e1 ->
    (match hBSe' with
    | BSBase _ _ _ hBSe1 -> lemma_bigstep_substitute_intros_base i rows e vs e1 v hBSse hBSe1)
  | XApps ea ->
    (match hBSe' with
    | BSApps _ _ _ hBSea ->
      BSApps _ _ _ (lemma_bigstep_substitute_intros_apps i rows e vs ea v hBSse hBSea))
  | XFby v0 e1 ->
    (match hBSe' with
    | BSFby1 _ _ _ -> BSFby1 [row] v0 (subst1' e1 i e)
    | BSFbyS _ _ _ _ _ hBS1 ->
      let BSsS prefix _ vs' _ _ hBSse' _ = hBSse in
      let hBS1' = lemma_bigstep_substitute_intros i prefix e vs' e1 v hBSse' hBS1 in
      BSFbyS row rows' v0 v _ hBS1')
  | XMu e1 ->
    (match hBSe' with
    | BSMu _ _ _ hBSe1 ->
      let valty = XMu?.valty e' in
      let hBSX = lemma_bigstep_substitute_intros i rows e vs (subst1 e1 (XMu e1)) v hBSse hBSe1 in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) (lift1 e valty)));
      BSMu _ (subst1' e1 (i + 1) (lift1 e valty)) _ hBSX)
  | XLet b e1 e2 ->
    (match hBSe' with
    | BSLet _ _ _ _ hBSX ->
      let hBSX' = lemma_bigstep_substitute_intros i rows e vs (subst1 e2 e1) v hBSse hBSX in
      lemma_subst_subst_distribute_le e2 0 i e1 e;
      assert_norm (subst1' (XLet b e1 e2) i e == XLet b (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)));
      BSLet _ (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)) _ hBSX')
  | XCheck p e1 ->
    (match hBSe' with
    | BSCheck _ _ _ v' hBS1 ->
      let hBS1' = lemma_bigstep_substitute_intros i rows e vs e1 v' hBSse hBS1 in
      BSCheck _ p (subst1' e1 i e) _ hBS1')
  | XContract ps er eg eb ->
    (match hBSe' with
    | BSContract _ ps _ _ _ _ hBSb ->
      let hBSb' = lemma_bigstep_substitute_intros i rows e vs eb v hBSse hBSb in
      assert_norm (subst1' (XContract ps er eg eb) i e == XContract ps (subst1' er i e) (subst1' eg (i + 1) (lift1 e a)) (subst1' eb i e));
      BSContract _ ps (subst1' er i e) (subst1' eg (i + 1) (lift1 e a)) (subst1' eb i e) v hBSb')

and lemma_bigstep_substitute_intros_apps
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp_apps t c a)
  (v: funty_sem t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep_apps (CP.row_zip2_lift1_dropped i rows vs) e' v):
    Tot (bigstep_apps rows (subst1_apps' e' i e) v) (decreases hBSe') =
  let row = List.Tot.hd rows in
  let rows' = List.Tot.tl rows in
  match e' with
  | XPrim p ->
    BSPrim rows p
  | XApp e1 e2 ->
    (match hBSe' with
    | BSApp _ _ _ v1 v2 hBS1 hBS2 ->
      let hBS1' = lemma_bigstep_substitute_intros_apps i rows e vs e1 v1 hBSse hBS1 in
      let hBS2' = lemma_bigstep_substitute_intros i rows e vs e2 v2 hBSse hBS2 in
      assert_norm (subst1_apps' (XApp e1 e2) i e == XApp (subst1_apps' e1 i e) (subst1' e2 i e));
      BSApp _ _ _ v1 v2 hBS1' hBS2')

(* used indirectly by lemma_bigstep_total *)
let lemma_bigstep_substitute_intros_no_dep_base
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp_base t c a { ~ (direct_dependency_base e' i) })
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (va: t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep_base (CP.row_lift1_dropped i r v :: CP.row_zip2_lift1_dropped i rows vs) e' va):
    Tot (bigstep (r :: rows) (subst1_base' e' i e) va) (decreases hBSe') =
  match e' with
  | XVal v -> BSBase _ _ _ (BSVal _ v)
  | XVar _ -> false_elim ()
  | XBVar i' ->
    assert (i <> i');
    if i' < i
    then BSBase _ _ _ (BSVar r rows i')
    else (
      CP.lemma_drop_get_index_gt c i (i' - 1);
      assert (C.opt_index (C.drop1 c i) (i' - 1) == Some (C.get_index c i'));
      assert_norm (subst1_base' (XBVar i') i e == XBase (XBVar #t #(C.drop1 c i) (i' - 1)));
      BSBase _ _ _ (BSVar r rows (i' - 1)))

let rec lemma_bigstep_substitute_intros_no_dep
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp t c a { ~ (direct_dependency e' i) })
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (va: t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep (CP.row_lift1_dropped i r v :: CP.row_zip2_lift1_dropped i rows vs) e' va):
    Tot (bigstep (r :: rows) (subst1' e' i e) va) (decreases hBSe') =
  match e' with
  | XBase e1 ->
    (match hBSe' with
    | BSBase _ _ _ hBSe1 -> lemma_bigstep_substitute_intros_no_dep_base i rows e vs e1 r v va hBSse hBSe1)
  | XApps ea ->
    (match hBSe' with
    | BSApps _ _ _ hBSea ->
      BSApps _ _ _ (lemma_bigstep_substitute_intros_no_dep_apps i rows e vs ea r v va hBSse hBSea))
  | XFby v0 e1 ->
    (match hBSe' with
    | BSFby1 _ _ _ -> BSFby1 [r] v0 (subst1' e1 i e)
    | BSFbyS _ _ _ _ _ hBS1 ->
      assert (Cons? rows);
      let hBS1' = lemma_bigstep_substitute_intros i rows e vs e1 va hBSse hBS1 in
      BSFbyS r rows v0 va (subst1' e1 i e) hBS1')
  | XMu e1 ->
    (match hBSe' with
    | BSMu _ _ _ hBSe1 ->
      let valty = XMu?.valty e' in
      lemma_direct_dependency_not_subst i 0 e1 (XMu e1);
      CP.lemma_dropCons valty c (i + 1);
      CP.lemma_get_index_Cons valty c i;
      assert (C.drop1 (valty :: c) (i + 1) == valty :: C.drop1 c i);
      let hBSX = lemma_bigstep_substitute_intros_no_dep i rows e vs (subst1 e1 (XMu e1)) r v va hBSse hBSe1 in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert_norm (subst1' (XMu e1) i e == XMu (subst1' e1 (i + 1) (lift1 e valty)));
      BSMu _ (subst1' e1 (i + 1) (lift1 e valty)) _ hBSX)

  | XLet b e1 e2 ->
    (match hBSe' with
    | BSLet _ _ _ _ hBSX ->
      lemma_direct_dependency_not_subst i 0 e2 e1;
      CP.lemma_dropCons b c (i + 1);
      CP.lemma_get_index_Cons b c i;
      assert (C.get_index (b :: c) (i + 1) == C.get_index c i);
      assert (C.drop1 (b :: c) (i + 1) == b :: C.drop1 c i);
      let hBSX' = lemma_bigstep_substitute_intros_no_dep i rows e vs (subst1 e2 e1) r v va hBSse hBSX in
      lemma_subst_subst_distribute_le e2 0 i e1 e;
      assert_norm (subst1' (XLet b e1 e2) i e == XLet b (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)));
      BSLet _ (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)) _ hBSX')

  | XCheck p e1 ->
    (match hBSe' with
    | BSCheck _ _ _ v' hBS1 ->
      let hBS1' = lemma_bigstep_substitute_intros_no_dep i rows e vs e1 r v v' hBSse hBS1 in
      BSCheck _ p (subst1' e1 i e) _ hBS1')

  | XContract ps er eg eb ->
    (match hBSe' with
    | BSContract _ _ _ _ _ v'' hBS1 ->
      let hBS1' = lemma_bigstep_substitute_intros_no_dep i rows e vs eb r v va hBSse hBS1 in
      BSContract _ ps (subst1' er i e) (subst1' eg (i + 1) (lift1 e a)) (subst1' eb i e) _ hBS1')

and lemma_bigstep_substitute_intros_no_dep_apps
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i))
  (vs: list (C.get_index (context_sem c) i) { List.Tot.length rows == List.Tot.length vs })
  (e': exp_apps t c a { ~ (direct_dependency_apps e' i) })
  (r: row (C.drop1 c i))
  (v: C.get_index (context_sem c) i)
  (va: funty_sem t.ty_sem a)
  (hBSse: bigsteps rows e vs)
  (hBSe': bigstep_apps (CP.row_lift1_dropped i r v :: CP.row_zip2_lift1_dropped i rows vs) e' va):
    Tot (bigstep_apps (r :: rows) (subst1_apps' e' i e) va) (decreases hBSe') =
  match e' with
  | XPrim p -> BSPrim _ p
  | XApp e1 e2 ->
    (match hBSe' with
    | BSApp _ _ _ v1 v2 hBS1 hBS2 ->
      assert_norm (direct_dependency_apps (XApp e1 e2) i == (direct_dependency_apps e1 i || direct_dependency e2 i));
      let hBS1' = lemma_bigstep_substitute_intros_no_dep_apps i rows e vs e1 r v v1 hBSse hBS1 in
      let hBS2' = lemma_bigstep_substitute_intros_no_dep i rows e vs e2 r v v2 hBSse hBS2 in
      assert_norm (subst1_apps' (XApp e1 e2) i e == XApp (subst1_apps' e1 i e) (subst1' e2 i e));
      BSApp _ _ _ v1 v2 hBS1' hBS2')

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
    lemma_bigstep_substitute_elim 0 rows e1 vs e2 v hBS1s hBS2'

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
        lemma_bigstep_substitute_elim 0 rows (XMu e) vs e (List.Tot.hd vs) hBSs hBS'

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
      lemma_bigstep_substitute_intros_no_dep 0 rows (XMu e) vs e row v' v hBSs hBS1 in
    BSMu (row :: rows) e v hBS''

(* used by transition system proof *)
let lemma_bigstep_base_total
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp_base t c a { causal_base e }):
    Tot (v: t.ty_sem a & bigstep_base rows e v) (decreases %[e; rows; 0]) =
  let hd = List.Tot.hd rows in
  let tl = List.Tot.tl rows in
  match e with
  | XVal v -> (| v, BSVal _ v |)
  | XVar _ -> false_elim ()
  | XBVar i -> (| CR.index (context_sem c) hd i, BSVar hd tl i |)

let rec lemma_bigstep_total
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp t c a { causal e }):
    Tot (v: t.ty_sem a & bigstep rows e v) (decreases %[e; rows; 0]) =
  let hd = List.Tot.hd rows in
  let tl = List.Tot.tl rows in
  match e with
  | XBase e1 ->
    let (| v, hBS |) = lemma_bigstep_base_total rows e1 in
    (| v, BSBase _ _ _ hBS |)
  | XApps ea ->
    let (| v, hBS |) = lemma_bigstep_apps_total rows ea in
    (| v, BSApps _ _ _ hBS |)
  | XFby v0 e1 ->
    (match rows with
    | [_] ->
      assert_norm (List.Tot.length rows == 1);
      (| v0, BSFby1 rows v0 e1 |)
    | latest :: prefix ->
      let (| v', hBSe1 |) = lemma_bigstep_total prefix e1 in
      (| v', BSFbyS latest prefix v0 v' e1 hBSe1 |))
  | XMu e1 ->
    let (| vs, hBSs |) = lemma_bigsteps_total tl e in
    let v' = t.val_default (XMu?.valty e) in
    let (| v, hBS0 |) = lemma_bigstep_total (CR.cons v' hd :: CR.zip2_cons vs tl) e1 in
    let hBS' = lemma_bigstep_substitute_intros_XMu tl e1 vs hd v v' hBSs hBS0 in
    (| v, hBS' |)

  | XLet b e1 e2 ->
    let (| vs, hBSs |) = lemma_bigsteps_total rows e1 in
    let (| v, hBS2 |) = lemma_bigstep_total (CR.zip2_cons vs rows) e2 in
    let hBS' = lemma_bigstep_substitute_intros 0 rows e1 vs e2 v hBSs hBS2 in
    (| v, BSLet rows e1 e2 v hBS' |)

  | XCheck p e1 ->
    let (| v1, hBS1 |) = lemma_bigstep_total rows e1 in
    (| (), BSCheck rows p e1 v1 hBS1 |)

  | XContract p er eg eb ->
    let (| v, hBSb |) = lemma_bigstep_total rows eb in
    (| v, BSContract rows p er eg eb v hBSb |)

and lemma_bigstep_apps_total
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp_apps t c a { causal_apps e }):
    Tot (v: funty_sem t.ty_sem a & bigstep_apps rows e v) (decreases %[e; rows; 0]) =
  let hd = List.Tot.hd rows in
  let tl = List.Tot.tl rows in
  match e with
  | XPrim p -> (| t.prim_sem p, BSPrim rows p |)
  | XApp f_e a_e ->
    assert_norm (causal_apps (XApp f_e a_e) == (causal_apps f_e && causal a_e));
    let (| f_v, hBSf |) = lemma_bigstep_apps_total rows f_e in
    let (| a_v, hBSa |) = lemma_bigstep_total rows a_e in
    (| f_v a_v, BSApp _ _ _ _ _ hBSf hBSa |)

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
    v: t.ty_sem a { bigstep rows e v } =
  let (| v, _ |) = lemma_bigstep_total rows e in
  v

let lemma_bigsteps_total_vs
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (rows: list (row c)) (e: exp t c a { causal e }):
    vs: list (t.ty_sem a) { List.Tot.length vs == List.Tot.length rows /\ bigsteps rows e vs } =
  let (| vs, _ |) = lemma_bigsteps_total rows e in
  vs

let lemma_bigstep_total_always
  (#t: table)
  (#c: context t)
  (rows: list (row c)) (row1: row c) (e: exp t c t.propty { causal e }):
  Lemma (requires (bigstep_always (row1 :: rows) e))
    (ensures (lemma_bigstep_total_v (row1 :: rows) e == true))
    [SMTPat (bigstep_always (row1 :: rows) e)] =
  let v = lemma_bigstep_total_v (row1 :: rows) e in
  // let (| v, hBS |) = lemma_bigstep_total (row1 :: rows) e in
  bigstep_deterministic_squash (row1 :: rows) e v true
