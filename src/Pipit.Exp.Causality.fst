(*TODO update to typed exprs*)
module Pipit.Exp.Causality

open Pipit.Exp.Base
open Pipit.Exp.Binding
open Pipit.Exp.Binding.Properties
open Pipit.Exp.Bigstep

module C = Pipit.Context

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

#push-options "--split_queries always"

(* used by lemma_causal_lift *)
let rec lemma_direct_dependency_lift (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) (i': C.index { i < i' /\ i' <= List.Tot.length 'c }) (t: Type):
    Lemma (ensures direct_dependency e i == direct_dependency (lift1' e i' t) i) (decreases e) =
  match e with
  | XVal _ | XVar _ | XBVar _ -> ()
  | XMu _ e1 ->
    lemma_direct_dependency_lift e1 (i + 1) (i' + 1) t

  | _ -> admit ()

(* used by lemma_causal_subst *)
let rec lemma_direct_dependency_not_subst (i: C.index { C.has_index 'c i }) (i': C.index { C.has_index 'c i' /\ i < i' })
  (e: exp 'c 'a { ~ (direct_dependency e i) /\ ~ (direct_dependency e i') })
  (p: exp (C.drop1 'c i') (C.get_index 'c i')):
    Lemma (ensures ~ (direct_dependency (subst1' e i' p) i)) (decreases e) =
  match e with
  | XVal _ | XVar _ | XBVar _ -> ()
  | XMu _ e1 ->
    lemma_direct_dependency_not_subst (i + 1) (i' + 1) e1 (lift1 p 'a)
  | _ -> admit ()

(* used by lemma_bigstep_substitute_intros_no_dep *)
let rec lemma_direct_dependency_not_subst' (i: C.index { C.has_index 'c i }) (i': C.index { C.has_index 'c i' /\ i' <= i })
  (e: exp 'c 'a { ~ (direct_dependency e (i + 1)) })
  (p: exp (C.drop1 'c i') (C.get_index 'c i') { ~ (direct_dependency p i ) }):
    Lemma (ensures ~ (direct_dependency (subst1' e i' p) i)) (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar _ -> ()
  | XMu _ e1 ->
    // TODO requires extra lemma lemma_direct_dependency_lift p i 0 'a;
    assume (~ (direct_dependency (lift1 p 'a) (i + 1)));
    lemma_direct_dependency_not_subst' (i + 1) (i' + 1) e1 (lift1 p 'a)
    // admit ()
  | _ -> admit ()

(* old statements, might be necessary *)
// let rec direct_dependency_not_subst (i: C.index { C.has_index 'c i }) (i': C.index { i' < i })
//   (e: exp 'c 'a { ~ (direct_dependency e i) })
//   (p: exp (C.drop1 'c i') (C.get_index 'c i') { ~ (direct_dependency p (i - 1)) }):
//     Lemma (ensures ~ (direct_dependency (subst1' e i' p) (i - 1))) (decreases e) =
// let rec direct_dependency_not_subst2 (i: C.index { C.has_index 'c i }) (i': C.index { C.has_index 'c i' /\ i < i' })
//   (e: exp 'c 'a)
//   (p: exp (C.drop1 'c i') (C.get_index 'c i')):
//     Lemma
//       (requires ~ (direct_dependency (subst1' e i' p) i))
//       (ensures ~ (direct_dependency e i)) (decreases e) =

(* used by lemma_bigstep_recursive_XMu *)
let rec lemma_bigstep_no_dep (e: exp (List.Tot.append 'c ('b :: 'd)) 'a { ~ (direct_dependency e (List.Tot.length 'c)) })
  (history: list (C.row (List.Tot.append 'c ('b :: 'd))))
  (rowc: C.row 'c)
  (rowd: C.row 'd)
  (b b': 'b)
  (a: 'a)
  (hBS: bigstep
    (C.row_append rowc (C.row_cons b rowd) :: history)
    e
    a):
  Tot (bigstep
        (C.row_append rowc (C.row_cons b' rowd) :: history)
        e a) (decreases hBS) =
  admit ()

  // let tv  = C.table_of_values (v :: row) in
  // let tv' = C.table_of_values (v' :: row) in
  // let t2  = C.table_map_append tv streams2 in
  // let t2' = C.table_map_append tv' streams2 in
  // let t  = C.table_map_append streams1 t2 in
  // let t' = C.table_map_append streams1 t2' in
  // match hBS with
  // | BSVal _ v ->
  //   C.table_const_const t t' v;
  //   BSVal _ v
  // | BSVar _ x ->
  //   assert (x <> inner1);
  //   if x < inner1
  //   then
  //   begin
  //       C.table_index_append_inner1 streams1 t2 x;
  //       C.table_index_append_inner1 streams1 t2' x;
  //       BSVar _ x
  //   end
  //   else
  //   begin
  //       C.table_index_append_inner2 streams1 t2 x;
  //       C.table_index_append_inner2 tv streams2 (x - inner1);
  //       C.table_index_append_inner2 streams1 t2' x;
  //       C.table_index_append_inner2 tv' streams2 (x - inner1);
  //       BSVar _ x
  //   end
  // | BSPrim2 _ p e1 e2 vs1 vs2 hBS1 hBS2 ->
  //   let hBS1' = bigstep_no_dep_no_difference e1 streams1 streams2 row v v' vs1 hBS1 in
  //   let hBS2' = bigstep_no_dep_no_difference e2 streams1 streams2 row v v' vs2 hBS2 in
  //   BSPrim2 _ p e1 e2 vs1 vs2 hBS1' hBS2'
  // | BSPre s0 ss e1 vs1 hBS1 ->
  //   let s0' = C.table_hd t' in
  //   BSPre s0' ss e1 vs1 hBS1
  // | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
  //   let hBS1' = bigstep_no_dep_no_difference e1 streams1 streams2 row v v' vs1 hBS1 in
  //   let hBS2' = bigstep_no_dep_no_difference e2 streams1 streams2 row v v' vs2 hBS2 in
  //   BSThen _ e1 e2 vs1 vs2 hBS1' hBS2'
  // | BSMu _ e1 vs1 hBS1 ->
  //   let e1' = subst e1 0 (XMu e1) in
  //   direct_dependency_not_subst (inner1 + 1) 0 e1 (XMu e1);
  //   let hBS1' = bigstep_no_dep_no_difference e1' streams1 streams2 row v v' vs1 hBS1 in
  //   BSMu _ e1 vs1 hBS1'
  // | BSLet _ e1 e2 vs2 hBS2 ->
  //   let e1' = subst e2 0 e1 in
  //   direct_dependency_not_subst (inner1 + 1) 0 e2 e1;
  //   let hBS2' = bigstep_no_dep_no_difference e1' streams1 streams2 row v v' vs2 hBS2 in
  //   BSLet _ e1 e2 vs2 hBS2'


(*
   We originally had a lemma that said:
   if expression e mentions variable x, then e[x := e'] mentions e'.
   we can re-state this as:
   if expression e mentions variable x, and e' mentions x', then e[x := e'] mentions x'.
   Do we need it?
*)

let rec lemma_causal_lift (e: exp 'c 'a) (i: C.index { i <= List.Tot.length 'c }) (t: Type):
  Lemma (requires (causal e))
        (ensures (causal (lift1' e i t)))
        (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar _ -> ()
  | XMu _ e1 ->
    lemma_causal_lift e1 (i + 1) t;
    lemma_direct_dependency_lift e1 0 (i + 1) t;
    ()
  | _ -> admit ()


let rec lemma_causal_subst (e: exp 'c 'a) (i: C.index { C.has_index 'c i })
  (p: exp (C.drop1 'c i) (C.get_index 'c i)):
  Lemma (requires (causal e /\ causal p /\ ~ (direct_dependency e i)))
        (ensures (causal (subst1' e i p)))
        (decreases e) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar _ -> ()
  | XMu _ e1 ->
    lemma_causal_lift p 0 'a;
    lemma_causal_subst e1 (i + 1) (lift1 p 'a);
    lemma_direct_dependency_not_subst 0 (i + 1) e1 (lift1 p 'a);
    ()
  | _ -> admit ()

(* used by ?? *)
let lemma_causal_subst__causal_XMu {| Pipit.Inhabited.inhabited 'a |}
  (e: exp ('a :: 'c) 'a):
  Lemma (requires causal (XMu e))
        (ensures causal (subst1' e 0 (XMu e))) =
  lemma_causal_subst e 0 (XMu e)

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
         assert (v == v');
         assert (v == List.Tot.hd vs);
        // TODO row_index lemmas
         assume (C.row_index 'c latest' i == v);
         BSVar latest' (List.Tot.tl rows') i)
    // else if i < i'
    else
      (match hBSe' with
       | BSVar latest prefix ix ->
         assert (ix == C.index_drop i' i 1);
         assert (C.row_index (C.drop1 'c i) latest ix == v');
         assert (C.get_index 'c i' == 'a);
         // TODO row_index lemmas
         assume (C.row_index 'c latest' i' == v');
         BSVar latest' (List.Tot.tl rows') i')
  | XMu _ e1 ->
    (match hBSe' with
    | BSMu _ _ e1' _ hBSe1 ->
      C.lemma_dropCons 'a 'c (i + 1);
      assume (C.get_index ('a :: 'c) (i + 1) == C.get_index 'c i);
      assume (C.drop1 ('a :: 'c) (i + 1) == 'a :: C.drop1 'c i);
      let lifted: exp (C.drop1 ('a :: 'c) (i + 1)) (C.get_index ('a :: 'c) (i + 1)) = lift1 e 'a in
      assert (e1' == subst1' e1 (i + 1) lifted);
      let se: exp ('a :: C.drop1 'c i) 'a = e1' in
      let se: exp (C.drop1 'c i) 'a = subst1 e1' (XMu e1') in
      lemma_subst_subst_distribute_XMu e1 i e;
      assert (subst1 (subst1' e1 (i + 1) lifted) (XMu e1') == subst1' (subst1 e1 (XMu e1)) i e);
      let hBSe1': bigstep rows se v' = hBSe1 in
      let hBSX = lemma_bigstep_substitute_elim i rows e vs (subst1 e1 (XMu e1)) v' hBSse hBSe1' in
      BSMu _ _ e1 _ hBSX
      // let hBSe1': bigstep rows' (subst1 e1' (subst1' (XMu e1) i e)) v' = hBSe1 in
      // let hBSe1' = lemma_bigstep_substitute_elim i rows vs _ _ hBSse hBSe1 in
      // admit ()
    )
  | _ -> admit ()

// let rec lemma_bigsteps_substitute_elim
//   (i: C.index { i < List.Tot.length 'c })
//   (rows: list (C.row (C.drop1 'c i)))
//   (e: exp (C.drop1 'c i) (C.get_index 'c i))
//   (vs: list (C.get_index 'c i) { List.Tot.length rows == List.Tot.length vs })
//   (e': exp 'c 'a)
//   (vs': list 'a { List.Tot.length rows == List.Tot.length vs' })
//   (hBSse: bigsteps rows e vs)
//   (hBSse': bigsteps rows (subst1' e' i e) vs'):
//     Tot (bigsteps (C.row_zip2_lift1_dropped i rows vs) e' vs') (decreases hBSse') =
//   match hBSse with
//   | BSs0 _ -> BSs0 e'
//   | BSsS rowsP _ vsP  row v  hBSseP  hBSe ->
//   match hBSse' with
//   | BSsS _     _ vs'P _   v' hBSse'P hBSe' ->
//     let hBSe'' = lemma_bigstep_substitute_elim i rows e vs e' v' hBSse hBSe' in
//     let rest = lemma_bigsteps_substitute_elim i rowsP e vsP e' vs'P hBSseP hBSse'P in
//     BSsS (C.row_zip2_lift1_dropped i rowsP vsP) _ vs'P (C.row_lift1_dropped i row v) v' rest hBSe''

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
    admit ()
  | XFby v0 e1 ->
    (match rows with
    | [] -> BSFby1 [r] v0 (subst1' e1 i e)
    | _ -> admit ()) // BSFbyS r rows v0 _ (subst1' e1 i e))
  | XMu _ e1 ->
    (match hBSe' with
    | BSMu inhabited _ _ _ hBSe1 ->
      lemma_direct_dependency_not_subst' i 0 e1 (XMu e1);
      assume (C.get_index ('a :: 'c) (i + 1) == C.get_index 'c i);
      assume (C.drop1 ('a :: 'c) (i + 1) == 'a :: C.drop1 'c i);
      let hBSX = lemma_bigstep_substitute_intros_no_dep i rows e vs (subst1 e1 (XMu e1)) r v a hBSse hBSe1 in
      lemma_subst_subst_distribute_XMu e1 i e;
      // let lifted: exp (C.drop1 ('a :: 'c) (i + 1)) (C.get_index ('a :: 'c) (i + 1)) = lift1 e 'a in
      // assert (subst1 (subst1' e1 (i + 1) lifted) (XMu e1') == subst1' (subst1 e1 (XMu e1)) i e);
      BSMu inhabited _ (subst1' e1 (i + 1) (lift1 e 'a)) _ hBSX)
  | _ -> admit ()

// let rec lemma_bigsteps_inverts_BSMu
//   {| Pipit.Inhabited.inhabited 'a |}
//   (rows: list (C.row 'c))
//   (e: exp ('a :: 'c) 'a)
//   (vs: list 'a { List.Tot.length rows == List.Tot.length vs })
//   (hBSs: bigsteps rows (XMu e) vs):
//          bigsteps rows (subst1 e (XMu e)) vs =
//   match hBSs with
//   | BSs0 _ -> BSs0 (subst1 e (XMu e))
//   | BSsS rows _ vs row v hBSs' hBS ->
//     let BSMu _ _ _ e1 hBS' = hBS in
//     let hBSs'' = lemma_bigsteps_inverts_BSMu rows e vs hBSs' in
//     BSsS rows _ vs row v hBSs'' hBS'


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
        assume (C.row_zip2_cons vs rows == C.row_zip2_lift1_dropped 0 rows vs);
        lemma_bigstep_substitute_elim 0 rows (XMu e) vs e (List.Tot.hd vs) hBSs hBS'

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
    // let hBSs': bigsteps rows (subst1 e (XMu e)) vs = lemma_bigsteps_inverts_BSMu rows e vs hBSs in
    // TODO context lemma
    assume (C.row_zip2_cons vs rows == C.row_zip2_lift1_dropped 0 rows vs);
    // let hBSs'': bigsteps (C.row_zip2_cons vs rows) e vs = lemma_bigsteps_substitute_elim 0 rows (XMu e) vs e vs hBSs hBSs' in
    let hBS'': bigstep (row :: rows) (subst1 e (XMu e)) v = lemma_bigstep_substitute_intros_no_dep 0 rows (XMu e) vs e row v' v hBSs hBS1 in
    BSMu _ (row :: rows) e v hBS''

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
    | [_] -> (| v0, BSFby1 rows v0 e1 |)
    | latest :: prefix ->
      let (| v', hBSe1 |) = lemma_bigstep_total prefix e1 in
      (| v', BSFbyS latest prefix v0 v' e1 hBSe1 |))

  | XMu _ e1 ->
    let (| vs, hBSs |) = lemma_bigsteps_total tl e in
    let v' = Pipit.Inhabited.get_inhabited in
    let (| v, hBS0 |) = lemma_bigstep_total (C.row_cons v' hd :: C.row_zip2_cons vs tl) e1 in
    let hBS' = lemma_bigstep_substitute_intros_XMu tl e1 vs hd v v' hBSs hBS0 in
    (| v, hBS' |)

  | _ -> admit ()
and lemma_bigsteps_total
  (rows: list (C.row 'c)) (e: exp 'c 'a { causal e }):
    Tot (vs: list 'a { List.Tot.length vs == List.Tot.length rows } & bigsteps rows e vs) (decreases %[e; rows; 1]) =
  match rows with
  | [] -> (| [], BSs0 e |)
  | r :: rows' ->
    let (| vs, hBSs |) = lemma_bigsteps_total rows' e in
    let (| v,  hBS1 |) = lemma_bigstep_total  rows  e in
    (| v :: vs, BSsS _ _ _ r v hBSs hBS1 |)
