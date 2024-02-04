(* Properties about checked semantics and substitution *)
module Pipit.Exp.Checked.Subst

open Pipit.Exp.Checked.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding
open Pipit.Exp.Binding.Properties

open Pipit.Exp.Causality

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties
module PM = Pipit.Prop.Metadata

module List = FStar.List.Tot

open FStar.Squash

#push-options "--split_queries always"

let subst_extend_dropped
  (#t: table)
  (#c: context t)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e }):
    Tot (r': (list (row c)) { List.length r' == List.length rows }) =
  CP.row_zip2_lift1_dropped i rows (lemma_bigsteps_total_vs rows e)

let rec lemma_bigstep_always_substitute
  (#t: table)
  (#c: context t)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp t c t.propty):
  Lemma (ensures (
    bigstep_always rows (subst1' e' i e) <==>
    bigstep_always (subst_extend_dropped i rows e) e'
  )) =
  match rows with
  | [] -> ()
  | r::rows' ->
    // TODO:ADMIT: squash, apply lemma_bigstep_substitute_elim, intros
    assume (bigstep rows (subst1' e' i e) true <==>
    bigstep (subst_extend_dropped i rows e) e' true);
    lemma_bigstep_always_substitute i rows' e e'

let rec lemma_check_substitute_elim
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp t c a)
  (hCKe': check mode rows (subst1' e' i e)):
    Tot (check mode (subst_extend_dropped i rows e) e') (decreases hCKe') =
  let rows' = subst_extend_dropped i rows e in
  match e' with
  | XBase b -> CkBase _ b
  | XApps ea ->
    let CkApps _ _ hCKa = hCKe' in
    CkApps _ _ (lemma_check_substitute_elim_apps mode i rows e ea hCKa)
  | XFby v1 e2 ->
    (match hCKe' with
    | CkFby1 _ _ _ -> CkFby1 rows' v1 e2
    | CkFbyS _ _ _ _ hCK2 ->
      CkFbyS (List.hd rows') (List.tl rows') v1 e2 (lemma_check_substitute_elim mode i (List.tl rows) e e2 hCK2))

  | XMu e1 ->
    let CkMu _ _ hCK1 = hCKe' in
    lemma_subst_subst_distribute_XMu e1 i e;
    let hCK1' = lemma_check_substitute_elim mode i rows e (subst1 e1 (XMu e1)) hCK1 in
    CkMu _ e1 hCK1'

  | XLet b e1 e2 ->
    let CkLet _ _ _ hCK = hCKe' in
    lemma_subst_subst_distribute_le e2 0 i e1 e;
    let hCK' = lemma_check_substitute_elim mode i rows e (subst1 e2 e1) hCK in
    CkLet _ e1 e2 hCK'

  | XCheck ps e1 ->
    let CkCheck _ _ _ hCK hBS = hCKe' in
    let hCK' = lemma_check_substitute_elim mode i rows e e1 hCK in
    lemma_bigstep_always_substitute i rows e e1;
    CkCheck _ ps e1 hCK' ()

  | XContract ps er eg eb ->
    let CkContract _ _ _ _ _ hTr hTrg hCr hCgb = hCKe' in
    lemma_bigstep_always_substitute i rows e er;
    lemma_bigstep_always_substitute i rows e (subst1 eg eb);

    let hTr' = () in
    let hTrg' = () in

    let hCr' = lemma_check_substitute_elim mode i rows e er hCr in

    let hCgb' = match hCgb with
      | Inl hN ->
        Inl ()
      | Inr (hCb,hCg) ->
        lemma_subst_subst_distribute_le eg 0 i eb e;
        let hCb' = lemma_check_substitute_elim mode i rows e eb hCb in
        let hCg' = lemma_check_substitute_elim mode i rows e (subst1 eg eb) hCg in
        Inr (hCb', hCg')
    in

    CkContract _ ps er eg eb hTr' hTrg' hCr' hCgb'

and lemma_check_substitute_elim_apps
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)) { Cons? rows })
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp_apps t c a)
  (hCKe': check_apps mode rows (subst1_apps' e' i e)):
    Tot (check_apps mode (subst_extend_dropped i rows e) e') (decreases hCKe') =
  let rows' = subst_extend_dropped i rows e in
  match e' with
  | XPrim f -> CkPrim rows' f
  | XApp ef ea ->
    let CkApp _ _ _ hCKf hCKa = hCKe' in
    let hCKf' = lemma_check_substitute_elim_apps mode i rows e ef hCKf in
    let hCKa' = lemma_check_substitute_elim mode i rows e ea hCKa in
    CkApp rows' _ _ hCKf' hCKa'


let lemma_check_substitute_intros_base
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp_base t c a)
  (hCKe: check mode rows e):
    Tot (check mode rows (subst1_base' e' i e)) =
  match e' with
  | XVal v -> CkBase rows (XVal v)
  | XVar x -> CkBase rows (XVar x)
  | XBVar i' ->
    if i = i'
    then hCKe
    else if i' < i
    then (
      CP.lemma_drop_get_index_lt c i i';
      let i': C.index_lookup (C.drop1 c i) = i' in
      let xv: exp_base t (C.drop1 c i) a = XBVar i' in
      CkBase rows xv
    ) else (
      CP.lemma_drop_get_index_gt c i (i' - 1);
      assert (C.opt_index (C.drop1 c i) (i' - 1) == Some (C.get_index c i'));
      assert_norm (subst1_base' (XBVar i') i e == XBase (XBVar #t #(C.drop1 c i) (i' - 1)));
      CkBase rows (XBVar (i' - 1)))

let rec lemma_check_substitute_intros
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp t c a)
  (hCKe: (r: list (row (C.drop1 c i)) { List.length r <= List.length rows }) -> check mode r e)
  (hCKe': check mode (subst_extend_dropped i rows e) e'):
    Tot (check mode rows (subst1' e' i e)) (decreases hCKe') =
  match e' with
  | XBase b ->
    lemma_check_substitute_intros_base mode i rows e b (hCKe rows)

  | XApps ea ->
    let CkApps _ _ hCKa = hCKe' in
    CkApps _ _ (lemma_check_substitute_intros_apps mode i rows e ea hCKe hCKa)

  | XFby v1 e2 ->
    (match hCKe' with
    | CkFby1 _ _ _ -> CkFby1 rows v1 (subst1' e2 i e)
    | CkFbyS _ _ _ _ hCK2 ->
      CkFbyS (List.hd rows) (List.tl rows) v1 (subst1' e2 i e) (lemma_check_substitute_intros mode i (List.tl rows) e e2 hCKe hCK2))

  | XMu e1 ->
    let CkMu _ _ hCK1 = hCKe' in
    lemma_subst_subst_distribute_XMu e1 i e;
    let hCK1' = lemma_check_substitute_intros mode i rows e (subst1 e1 (XMu e1)) hCKe hCK1 in
    CkMu _ (subst1' e1 (i + 1) (lift1 e a)) hCK1'

  | XLet b e1 e2 ->
    let CkLet _ _ _ hCK = hCKe' in
    lemma_subst_subst_distribute_le e2 0 i e1 e;
    let hCK' = lemma_check_substitute_intros mode i rows e (subst1 e2 e1) hCKe hCK in
    CkLet _ (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)) hCK'

  | XCheck ps e1 ->
    let CkCheck _ _ _ hCK hBS = hCKe' in
    let hCK' = lemma_check_substitute_intros mode i rows e e1 hCKe hCK in
    lemma_bigstep_always_substitute i rows e e1;
    CkCheck _ ps (subst1' e1 i e) hCK' ()

  | XContract ps er eg eb ->
    let CkContract _ _ _ _ _ hTr hTrg hCr hCgb = hCKe' in
    lemma_bigstep_always_substitute i rows e er;
    lemma_bigstep_always_substitute i rows e (subst1 eg eb);

    let hTr' = () in
    let hTrg' = () in

    let hCr' = lemma_check_substitute_intros mode i rows e er hCKe hCr in

    let hCgb' = match hCgb with
      | Inl hN ->
        Inl ()
      | Inr (hCb,hCg) ->
        lemma_subst_subst_distribute_le eg 0 i eb e;
        let hCb' = lemma_check_substitute_intros mode i rows e eb hCKe hCb in
        let hCg' = lemma_check_substitute_intros mode i rows e (subst1 eg eb) hCKe hCg in
        Inr (hCb', hCg')
    in

    CkContract _ ps (subst1' er i e) (subst1' eg (i + 1) (lift1 e a)) (subst1' eb i e) hTr' hTrg' hCr' hCgb'

and lemma_check_substitute_intros_apps
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp_apps t c a)
  (hCKe: (r: list (row (C.drop1 c i)) { List.length r <= List.length rows }) -> check mode r e)
  (hCKe': check_apps mode (subst_extend_dropped i rows e) e'):
    Tot (check_apps mode rows (subst1_apps' e' i e)) (decreases hCKe') =
  match e' with
  | XPrim f -> CkPrim rows f
  | XApp ef ea ->
    let CkApp _ _ _ hCKf hCKa = hCKe' in
    let hCKf' = lemma_check_substitute_intros_apps mode i rows e ef hCKe hCKf in
    let hCKa' = lemma_check_substitute_intros mode i rows e ea hCKe hCKa in
    CkApp rows _ _ hCKf' hCKa'



let lemma_check_substitute_intros_no_dep_base
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp_base t c a { ~ (direct_dependency_base e' i) }):
    Tot (check mode rows (subst1_base' e' i e)) =
  match e' with
  | XVal v -> CkBase rows (XVal v)
  | XVar x -> CkBase rows (XVar x)
  | XBVar i' ->
    assert (i <> i');
    if i' < i
    then (
      CP.lemma_drop_get_index_lt c i i';
      let i': C.index_lookup (C.drop1 c i) = i' in
      let xv: exp_base t (C.drop1 c i) a = XBVar i' in
      CkBase rows xv
    ) else (
      CP.lemma_drop_get_index_gt c i (i' - 1);
      assert (C.opt_index (C.drop1 c i) (i' - 1) == Some (C.get_index c i'));
      assert_norm (subst1_base' (XBVar i') i e == XBase (XBVar #t #(C.drop1 c i) (i' - 1)));
      CkBase rows (XBVar (i' - 1)))

let rec lemma_check_substitute_intros_no_dep
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp t c a { ~ (direct_dependency e' i) })
  (hCKe: (r: list (row (C.drop1 c i)) { List.length r < List.length rows }) -> check mode r e)
  (hCKe': check mode (subst_extend_dropped i rows e) e'):
    Tot (check mode rows (subst1' e' i e)) (decreases hCKe') =
  match e' with
  | XBase b ->
    lemma_check_substitute_intros_no_dep_base mode i rows e b

  | XApps ea ->
    let CkApps _ _ hCKa = hCKe' in
    CkApps _ _ (lemma_check_substitute_intros_no_dep_apps mode i rows e ea hCKe hCKa)

  | XFby v1 e2 ->
    (match hCKe' with
    | CkFby1 _ _ _ -> CkFby1 rows v1 (subst1' e2 i e)
    | CkFbyS _ _ _ _ hCK2 ->
      CkFbyS (List.hd rows) (List.tl rows) v1 (subst1' e2 i e) (lemma_check_substitute_intros mode i (List.tl rows) e e2 hCKe hCK2))

  | XMu e1 ->
    let CkMu _ _ hCK1 = hCKe' in
    lemma_direct_dependency_not_subst i 0 e1 (XMu e1);
    lemma_subst_subst_distribute_XMu e1 i e;
    let hCK1' = lemma_check_substitute_intros_no_dep mode i rows e (subst1 e1 (XMu e1)) hCKe hCK1 in
    CkMu _ (subst1' e1 (i + 1) (lift1 e a)) hCK1'

  | XLet b e1 e2 ->
    let CkLet _ _ _ hCK = hCKe' in
    lemma_direct_dependency_not_subst i 0 e2 e1;
    lemma_subst_subst_distribute_le e2 0 i e1 e;
    let hCK' = lemma_check_substitute_intros_no_dep mode i rows e (subst1 e2 e1) hCKe hCK in
    CkLet _ (subst1' e1 i e) (subst1' e2 (i + 1) (lift1 e b)) hCK'

  | XCheck ps e1 ->
    let CkCheck _ _ _ hCK hBS = hCKe' in
    let hCK' = lemma_check_substitute_intros_no_dep mode i rows e e1 hCKe hCK in
    lemma_bigstep_always_substitute i rows e e1;
    CkCheck _ ps (subst1' e1 i e) hCK' ()

  | XContract ps er eg eb ->
    let CkContract _ _ _ _ _ hTr hTrg hCr hCgb = hCKe' in
    lemma_bigstep_always_substitute i rows e er;
    lemma_bigstep_always_substitute i rows e (subst1 eg eb);

    let hTr' = () in
    let hTrg' = () in

    let hCr' = lemma_check_substitute_intros_no_dep mode i rows e er hCKe hCr in

    let hCgb' = match hCgb with
      | Inl hN ->
        Inl ()
      | Inr (hCb,hCg) ->
        lemma_direct_dependency_not_subst i 0 eg eb;
        lemma_subst_subst_distribute_le eg 0 i eb e;
        let hCb' = lemma_check_substitute_intros_no_dep mode i rows e eb hCKe hCb in
        let hCg' = lemma_check_substitute_intros_no_dep mode i rows e (subst1 eg eb) hCKe hCg in
        Inr (hCb', hCg')
    in

    let hC' = CkContract _ ps (subst1' er i e) (subst1' eg (i + 1) (lift1 e a)) (subst1' eb i e) hTr' hTrg' hCr' hCgb' in
    admit ()

and lemma_check_substitute_intros_no_dep_apps
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (mode: PM.check_mode)
  (i: C.index_lookup c)
  (rows: list (row (C.drop1 c i)))
  (e: exp t (C.drop1 c i) (C.get_index c i) { causal e })
  (e': exp_apps t c a { ~ (direct_dependency_apps e' i) })
  (hCKe: (r: list (row (C.drop1 c i)) { List.length r < List.length rows }) -> check mode r e)
  (hCKe': check_apps mode (subst_extend_dropped i rows e) e'):
    Tot (check_apps mode rows (subst1_apps' e' i e)) (decreases hCKe') =
  match e' with
  | XPrim f -> CkPrim rows f
  | XApp ef ea ->
    let CkApp _ _ _ hCKf hCKa = hCKe' in
    let hCKf' = lemma_check_substitute_intros_no_dep_apps mode i rows e ef hCKe hCKf in
    let hCKa' = lemma_check_substitute_intros_no_dep mode i rows e ea hCKe hCKa in
    CkApp rows _ _ hCKf' hCKa'



let rec lemma_check_nil
  (#t: table) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (e: exp t c a { causal e }):
    Tot (check mode [] e)
      (decreases e)
  // TODO:ADMIT: needs fancy substitution like in Causality?
  = match e with
  | XBase b -> CkBase _ b
  | XApps _ -> admit ()
  | XFby v e1 -> CkFby1 [] v e1
  | XMu e1 ->
    let hCk = lemma_check_nil mode e1 in
    let hCk' = lemma_check_substitute_intros_no_dep
      mode 0 [] (XMu e1) e1
      (fun r -> false_elim ())
      hCk
    in
    CkMu [] e1 hCk'
  | XLet b e1 e2 ->
    let hCk1 = lemma_check_nil mode e1 in
    let hCk2 = lemma_check_nil mode e2 in
    let hCk2' = lemma_check_substitute_intros
      mode 0 [] e1 e2
      (fun r -> hCk1) hCk2
    in
    CkLet [] e1 e2 hCk2'

  | _ -> admit ()
