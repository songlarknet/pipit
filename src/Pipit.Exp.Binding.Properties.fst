(* Properties about lifting and substitution.
   The proofs here are quite involved. I think the theory for contexts needs to
   be cleaned up a bit.
   The main lemma we want is that substitution can be reordered like:
     (e0[x1 := e1])[x2 := e2] == (e0[x2 := e2])[x1 := e1[x2 := e2]]
   *)
module Pipit.Exp.Binding.Properties

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.Exp.Binding

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties
module PM = Pipit.Prop.Metadata

// #push-options "--split_queries always"
#push-options "--fuel 1 --ifuel 1"

let lemma_lift_lift_commute_base (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (i1: C.index_insert c) (i2: C.index { i2 <= i1 }) (t1 t2: ('t).ty):
  Lemma (ensures (lift1_base' (lift1_base' e i1 t1) i2 t2 === lift1_base' (lift1_base' e i2 t2) (i1 + 1) t1)) =
  CP.lemma_lift_lift_commute c i1 i2 t1 t2

let rec lemma_lift_lift_commute (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i1: C.index_insert c) (i2: C.index { i2 <= i1 }) (t1 t2: ('t).ty):
  Lemma (ensures (lift1' (lift1' e i1 t1) i2 t2 === lift1' (lift1' e i2 t2) (i1 + 1) t1))
    (decreases e) =
  let lemma_lift_lift_commute_bind (#a #b: ('t).ty) (e': exp_bind 't b c a { e' << e }):
    Lemma (ensures (lift1_bind' (lift1_bind' e' i1 t1) i2 t2 === lift1_bind' (lift1_bind' e' i2 t2) (i1 + 1) t1)) =
     CP.lemma_lift_lift_commute c i1 i2 t1 t2;
     lemma_lift_lift_commute e' (i1 + 1) (i2 + 1) t1 t2
  in
  CP.lemma_lift_lift_commute c i1 i2 t1 t2;
  match e with
  | XBase b -> lemma_lift_lift_commute_base b i1 i2 t1 t2
  | XApps e1 -> lemma_lift_lift_commute_apps e1 i1 i2 t1 t2
  | XFby v e1 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2
  | XMu e1 ->
    lemma_lift_lift_commute_bind e1
  | XLet _ e1 e2 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2;
    lemma_lift_lift_commute_bind e2
  | XCheck _ e1 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2
  | XContract _ r g i ->
    lemma_lift_lift_commute r i1 i2 t1 t2;
    lemma_lift_lift_commute_bind g;
    lemma_lift_lift_commute i i1 i2 t1 t2

and lemma_lift_lift_commute_apps (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (i1: C.index_insert c) (i2: C.index { i2 <= i1 }) (t1 t2: ('t).ty):
  Lemma (ensures (lift1_apps' (lift1_apps' e i1 t1) i2 t2 === lift1_apps' (lift1_apps' e i2 t2) (i1 + 1) t1))
    (decreases e) =
  CP.lemma_lift_lift_commute c i1 i2 t1 t2;
  match e with
  | XPrim _ -> ()
  | XApp f e1 ->
    lemma_lift_lift_commute_apps f  i1 i2 t1 t2;
    lemma_lift_lift_commute      e1 i1 i2 t1 t2

let lemma_subst_lift_id_base (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (i: C.index_insert c) (t: ('t).ty) (p: exp 't c t):
  Lemma (ensures (subst1_base' (lift1_base' e i t) i p == XBase e)) =
    ()

let rec lemma_subst_lift_id (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i: C.index_insert c) (t: ('t).ty) (p: exp 't c t):
  Lemma (ensures (subst1' (lift1' e i t) i p == e))
    (decreases e) =

  let lemma_subst_lift_id_bind (#a #b: ('t).ty) (e': exp_bind 't b c a { e' << e }):
  Lemma (ensures (subst1_bind' (lift1_bind' e' i t) i p == e')) =
    lemma_subst_lift_id e' (i + 1) t (lift1 p b)
  in
  match e with
  | XBase e1 -> lemma_subst_lift_id_base e1 i t p
  | XApps e1 -> lemma_subst_lift_id_apps e1 i t p
  | XFby v e1 ->
    lemma_subst_lift_id e1 i t p
  | XMu e1 ->
    lemma_subst_lift_id_bind e1
  | XLet b e1 e2 ->
    lemma_subst_lift_id e1 i t p;
    lemma_subst_lift_id_bind e2
  | XCheck _ e1 ->
    lemma_subst_lift_id e1 i t p
  | XContract _ r g impl ->
    lemma_subst_lift_id r i t p;
    lemma_subst_lift_id_bind g;
    lemma_subst_lift_id impl i t p

and lemma_subst_lift_id_apps (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (i: C.index_insert c) (t: ('t).ty) (p: exp 't c t):
  Lemma (ensures (subst1_apps' (lift1_apps' e i t) i p == e))
    (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    lemma_subst_lift_id_apps e1 i t p;
    lemma_subst_lift_id e2 i t p

private
unfold
let _lift_of_drop (#c: context 't) (i1: C.index_lookup c) (p: exp 't (C.drop1 c i1) (C.get_index c i1)) (t: ('t).ty):
  exp 't (C.drop1 (t :: c) (i1 + 1)) (C.get_index (t :: c) (i1 + 1)) =
  lift1 p t

(* Lift distributes over subst:
     lift (e[x' := e']) == (lift e)[S x' := lift e']

   These proofs are a bit involved, so I've split them out into separate lemmas
   for different cases.
*)
let lemma_lift_subst_distribute_le_def (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i1: C.index_lookup c) (i2: C.index { i2 <= i1 }) (t2: ('t).ty) (p: exp 't (C.drop1 c i1) (C.get_index c i1)): prop =
    CP.lemma_lift_drop_commute_le c i1 i2 t2;
    lift1' (subst1' e i1 p) i2 t2 == subst1' (lift1' e i2 t2) (i1 + 1) (lift1' p i2 t2)

(* Disabling inversion seems to help solve the actual proof part, but the
   inversion is necessary for the induction / termination proof. So we prove the
   separate lemmas with inversion disabled. *)
#push-options "--fuel 1 --ifuel 0 --split_queries always"

let lemma_lift_subst_distribute_le_base (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (i1: C.index_lookup c) (i2: C.index { i2 <= i1 }) (t2: ('t).ty) (p: exp 't (C.drop1 c i1) (C.get_index c i1)):
  Lemma (ensures (
    lemma_lift_subst_distribute_le_def (XBase e) i1 i2 t2 p)) =
  CP.lemma_lift_drop_commute_le c i1 i2 t2;
  CP.lemma_lift_get_index_gt c i1 i2 t2;
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar i -> ()

#pop-options

#push-options "--fuel 1 --ifuel 1 --split_queries always"

let rec lemma_lift_subst_distribute_le (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i1: C.index_lookup c) (i2: C.index { i2 <= i1 }) (t2: ('t).ty) (p: exp 't (C.drop1 c i1) (C.get_index c i1)):
  Lemma (ensures (lemma_lift_subst_distribute_le_def e i1 i2 t2 p))
    (decreases e) =
  CP.lemma_lift_drop_commute_le c i1 i2 t2;
  CP.lemma_lift_get_index_gt c i1 i2 t2;
  let bind (#a #b: ('t).ty) (e': exp_bind 't b c a { e' << e }):
    Lemma (ensures (lemma_lift_subst_distribute_le_def e' (i1 + 1) (i2 + 1) t2 (_lift_of_drop i1 p b))) =
      let p' = _lift_of_drop i1 p b in
      lemma_lift_subst_distribute_le e' (i1 + 1) (i2 + 1) t2 p';
      ()
  in
  match e with
  | XBase e1 -> lemma_lift_subst_distribute_le_base e1 i1 i2 t2 p
  | XApps e1 -> lemma_lift_subst_distribute_le_apps e1 i1 i2 t2 p
  | XFby v e1 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    ()
  | XMu e1 ->
    lemma_lift_lift_commute p i2 0 t2 a;
    bind e1
  | XLet b e1 e2 ->
    lemma_lift_lift_commute p i2 0 t2 b;
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    bind e2
  | XCheck _ e1 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p
  | XContract _ r g i ->
    lemma_lift_lift_commute p i2 0 t2 a;
    lemma_lift_subst_distribute_le r i1 i2 t2 p;
    bind g;
    lemma_lift_subst_distribute_le i i1 i2 t2 p

and lemma_lift_subst_distribute_le_apps (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (i1: C.index_lookup c) (i2: C.index { i2 <= i1 }) (t2: ('t).ty) (p: exp 't (C.drop1 c i1) (C.get_index c i1)):
  Lemma (ensures (
    CP.lemma_lift_drop_commute_le c i1 i2 t2;
    lift1_apps' (subst1_apps' e i1 p) i2 t2 == subst1_apps' (lift1_apps' e i2 t2) (i1 + 1) (lift1' p i2 t2)))
    (decreases e) =
  CP.lemma_lift_drop_commute_le c i1 i2 t2;
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    lemma_lift_subst_distribute_le_apps e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 i1 i2 t2 p

let lemma_subst_subst_distribute_le_def (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)) =
    CP.lemma_drop_drop_commute c i1 i2;
    CP.lemma_drop_get_index_lt c (i2 + 1) i1;
    subst1' (subst1' e i1 p1) i2 p2 ==
    subst1' (subst1' e (i2 + 1) (lift1' p2 i1 (C.get_index c i1))) i1 (subst1' p1 i2 p2)

#push-options "--fuel 1 --ifuel 0"

private
let lemma_subst_subst_distribute_le_base_XBVar_Si2 (#c: context 't) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma (ensures lemma_subst_subst_distribute_le_def (XBase (XBVar (i2 + 1))) i1 i2 p1 p2) =
  CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
  CP.lemma_lift_drop_eq c i1;
  lemma_subst_lift_id p2 i1 (C.get_index c i1) (subst1' p1 i2 p2);
  ()

#pop-options

private
let lemma_subst_subst_distribute_le_base (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma (ensures
    lemma_subst_subst_distribute_le_def (XBase e) i1 i2 p1 p2) =
  CP.lemma_drop_drop_commute c i1 i2;
  CP.lemma_drop_get_index_lt c (i2 + 1) i1;
  match e with
  | XVal v -> ()
  | XVar _ -> ()
  | XBVar i' ->
    if i' = i2 + 1
    then lemma_subst_subst_distribute_le_base_XBVar_Si2 i1 i2 p1 p2
    else if i' = i1
    then ()
    else ()

private
unfold
let _lift_of_drop2 (#c: context 't) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)) (t: ('t).ty):
  exp 't (C.drop1 (C.drop1 (t :: c) (i1 + 1)) (i2 + 1))
    (C.get_index (C.drop1 (t :: c) (i1 + 1)) (i2 + 1)) =
  lift1 p t


private
let lemma_subst_subst_distribute_le_context_facts
  (#c: context 't)
  (te: ('t).ty)
  (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }):
  Lemma
    (ensures (
      // CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
      (te :: C.drop1 (C.drop1 c (i2 + 1)) i1 == C.drop1 (C.drop1 (te :: c) (i2 + 2)) (i1 + 1)) /\
      (C.get_index (te :: c) (i2 + 2) == C.get_index (te :: C.drop1 c i1) (i2 + 1)) /\
      (C.drop1 (te :: c) (i2 + 2) == C.lift1 (C.drop1 (te :: C.drop1 c i1) (i2 + 1)) (i1 + 1) (C.get_index c i1)))) =

  CP.lemma_drop_drop_commute c i1 i2;
  CP.lemma_drop_get_index_lt c (i2 + 1) i1;

  assert (C.get_index c (i2 + 1) == C.get_index (C.drop1 c i1) i2);
  assert (C.get_index (te :: c) (i2 + 2) == C.get_index (te :: C.drop1 c i1) (i2 + 1));
  ()

module T = FStar.Tactics
let tac_unfold_env (): T.Tac unit =
  ignore (T.repeat T.revert);
  T.norm [delta_only [`%lemma_subst_subst_distribute_le_def; `%lemma_lift_subst_distribute_le_def; `%_lift_of_drop; `%_lift_of_drop2; `%lift1]];
  ignore (T.repeat T.intro)



#push-options "--fuel 1 --ifuel 0"
// --z3rlimit 20
private
let lemma_subst_subst_distribute_le_bind
  (#c: context 't)
  (#te #tf: ('t).ty)
  (e: exp 't (te :: c) tf) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma
    (requires (lemma_subst_subst_distribute_le_def e (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 te) (_lift_of_drop2 i1 i2 p2 te)))
    (ensures (
      CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
      lemma_subst_subst_distribute_le_context_facts te i1 i2;
      (subst1' (subst1' e (i1 + 1) (_lift_of_drop i1 p1 te)) (i2 + 1) (_lift_of_drop2 i1 i2 p2 te)) ==
      (subst1' (subst1' e (i2 + 2) (lift1 (lift1' p2 i1 (C.get_index c i1)) te)) (i1 + 1) (lift1 (subst1' p1 i2 p2) te)))) =
  // let subst_req: squash (lemma_subst_subst_distribute_le_def e (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 te) (_lift_of_drop2 i1 i2 p2 te)) = () in
  // norm_spec [delta_only [`%lemma_subst_subst_distribute_le_def; `%_lift_of_drop; `%_lift_of_drop2; `%lift1]] (lemma_subst_subst_distribute_le_def e (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 te) (_lift_of_drop2 i1 i2 p2 te));

  lemma_lift_lift_commute p2 i1 0 (C.get_index c i1) te;
  lemma_lift_subst_distribute_le p1 i2 0 te p2;
  // assert (lift1' (subst1' p1 i2 p2) 0 te == subst1' (lift1' p1 0 te) (i2 + 1) (lift1' p2 0 te));
  lemma_subst_subst_distribute_le_context_facts te i1 i2;
  CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
  CP.lemma_lift_drop_eq c i1;
  CP.lemma_drop_drop_commute c i1 i2;
  CP.lemma_drop_get_index_lt c (i2 + 1) i1;

  assert (
      (subst1' (subst1' e (i1 + 1) (_lift_of_drop i1 p1 te)) (i2 + 1) (_lift_of_drop2 i1 i2 p2 te)) ==
      (subst1' (subst1' e (i2 + 2) (lift1 (lift1' p2 i1 (C.get_index c i1)) te)) (i1 + 1) (lift1 (subst1' p1 i2 p2) te)))
    by (
      tac_unfold_env ();
      // T.dump "T";
      ())



private
let lemma_subst_subst_distribute_le_XMu
  (#c: context 't)
  (#te: ('t).ty)
  (e: exp 't (te :: c) te) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma
    (requires (lemma_subst_subst_distribute_le_def e (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 te) (_lift_of_drop2 i1 i2 p2 te)))
    (ensures (lemma_subst_subst_distribute_le_def (XMu e) i1 i2 p1 p2)) =
  lemma_subst_subst_distribute_le_bind e i1 i2 p1 p2;
  CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
  assert (
    subst1' (subst1' (XMu e) i1 p1) i2 p2 ==
    subst1' (subst1' (XMu e) (i2 + 1) (lift1' p2 i1 (C.get_index c i1))) i1 (subst1' p1 i2 p2)
  ) by (tac_unfold_env ())

private
let lemma_subst_subst_distribute_le_XLet
  (#c: context 't)
  (#te #tf: ('t).ty)
  (e1: exp 't c te) (e2: exp 't (te :: c) tf) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma
    (requires (
      lemma_subst_subst_distribute_le_def e1 i1 i2 p1 p2 /\
      lemma_subst_subst_distribute_le_def e2 (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 te) (_lift_of_drop2 i1 i2 p2 te)))
    (ensures (lemma_subst_subst_distribute_le_def (XLet te e1 e2) i1 i2 p1 p2)) =
  lemma_subst_subst_distribute_le_bind e2 i1 i2 p1 p2;
  CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
  assert (
    subst1' (subst1' (XLet te e1 e2) i1 p1) i2 p2 ==
    subst1' (subst1' (XLet te e1 e2) (i2 + 1) (lift1' p2 i1 (C.get_index c i1))) i1 (subst1' p1 i2 p2)
  ) by (tac_unfold_env ())

private
let lemma_subst_subst_distribute_le_XContract
  (#c: context 't)
  (#valty: ('t).ty)
  (status: PM.contract_status)
  (er: exp 't c ('t).propty) (eg: exp 't (valty :: c) ('t).propty) (ei: exp 't c valty)
  (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma
    (requires (
      lemma_subst_subst_distribute_le_def er i1 i2 p1 p2 /\
      lemma_subst_subst_distribute_le_def eg (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 valty) (_lift_of_drop2 i1 i2 p2 valty) /\
      lemma_subst_subst_distribute_le_def ei i1 i2 p1 p2))
    (ensures (lemma_subst_subst_distribute_le_def (XContract status er eg ei) i1 i2 p1 p2)) =
  lemma_subst_subst_distribute_le_bind eg i1 i2 p1 p2;
  CP.lemma_lift_drop_commute_le (C.drop1 c i1) i2 i1 (C.get_index c i1);
    // CP.lemma_drop_drop_commute c i1 i2;
    // CP.lemma_drop_get_index_lt c (i2 + 1) i1;
  assert (
    subst1' (subst1' (XContract status er eg ei) i1 p1) i2 p2 ==
    subst1' (subst1' (XContract status er eg ei) (i2 + 1) (lift1' p2 i1 (C.get_index c i1))) i1 (subst1' p1 i2 p2)
  ) by (tac_unfold_env ())

#pop-options

// (Error 19) Subtyping check failed; expected type exp ’t
//   (C.drop1 (C.drop1 (b :: c) (i1 + 1)) (i2 + 1))
//   (C.get_index (C.drop1 (b :: c) (i1 + 1)) (i2 + 1)); got type exp ’t (C.drop1 (b :: C.drop1 c i1) (i2 + 1)) (C.get_index (b :: C.drop1 c i1) (i2 + 1))

let rec lemma_subst_subst_distribute_le (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma (ensures
    lemma_subst_subst_distribute_le_def e i1 i2 p1 p2)
    (decreases e) =
  CP.lemma_drop_drop_commute c i1 i2;
  CP.lemma_drop_get_index_lt c (i2 + 1) i1;
  let bind (#a #b: ('t).ty) (e': exp_bind 't b c a { e' << e }):
    Lemma (ensures
      lemma_subst_subst_distribute_le_def e' (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 b) (_lift_of_drop2 i1 i2 p2 b)) =
      lemma_subst_subst_distribute_le e' (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 b) (_lift_of_drop2 i1 i2 p2 b)
  in
  match e with
  | XBase e1 ->
    lemma_subst_subst_distribute_le_base e1 i1 i2 p1 p2

  | XApps e1 ->
    lemma_subst_subst_distribute_le_apps e1 i1 i2 p1 p2

  | XFby v e1 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2

  | XCheck _ e1 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2

  | XMu e1 ->
    bind e1;
    lemma_subst_subst_distribute_le_XMu e1 i1 i2 p1 p2

  | XLet b e1 e2 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2;
    bind e2;
    lemma_subst_subst_distribute_le_XLet e1 e2 i1 i2 p1 p2

  | XContract status r g i ->
    lemma_subst_subst_distribute_le r i1 i2 p1 p2;
    bind g;
    lemma_subst_subst_distribute_le i i1 i2 p1 p2;
    lemma_subst_subst_distribute_le_XContract status r g i i1 i2 p1 p2

and lemma_subst_subst_distribute_le_apps (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length c - 1 }) (p1: exp 't (C.drop1 c i1) (C.get_index c i1)) (p2: exp 't (C.drop1 (C.drop1 c i1) i2) (C.get_index (C.drop1 c i1) i2)):
  Lemma (ensures
    (CP.lemma_drop_drop_commute c i1 i2;
    CP.lemma_drop_get_index_lt c (i2 + 1) i1;
    subst1_apps' (subst1_apps' e i1 p1) i2 p2 ==
    subst1_apps' (subst1_apps' e (i2 + 1) (lift1' p2 i1 (C.get_index c i1))) i1 (subst1' p1 i2 p2)))
    (decreases e) =
  CP.lemma_drop_drop_commute c i1 i2;
  CP.lemma_drop_get_index_lt c (i2 + 1) i1;
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    lemma_subst_subst_distribute_le_apps e1 i1 i2 p1 p2;
    lemma_subst_subst_distribute_le e2 i1 i2 p1 p2



let lemma_subst_subst_distribute_XMu (#c: context 't) (#te: ('t).ty) (e: exp 't (te :: c) te) (i: C.index_lookup c) (p: exp 't (C.drop1 c i) (C.get_index c i)):
  Lemma (ensures
    subst1' (subst1 e (XMu e)) i p ==
    subst1 (subst1' e (i + 1) (lift1 p te)) (XMu (subst1' e (i + 1) (lift1 p te))))
    =
  lemma_subst_subst_distribute_le e 0 i (XMu e) p
