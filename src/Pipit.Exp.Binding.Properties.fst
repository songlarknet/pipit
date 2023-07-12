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

#push-options "--split_queries always"

#push-options "--fuel 1 --ifuel 1"

private
let lemma_lift_lift_commute_XApp (e1: exp 'c ('b -> 'a)) (e2: exp 'c 'b) (i1: C.index { i1 <= List.Tot.length 'c }) (i2: C.index { i2 <= i1 }) (t1 t2: Type):
  Lemma
    (requires (lift1' (lift1' e1 i1 t1) i2 t2 === lift1' (lift1' e1 i2 t2) (i1 + 1) t1) /\
              (lift1' (lift1' e2 i1 t1) i2 t2 === lift1' (lift1' e2 i2 t2) (i1 + 1) t1))
    (ensures (lift1' (lift1' (XApp e1 e2) i1 t1) i2 t2 === lift1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) t1))
     =
  C.lemma_lift_lift_commute 'c i1 i2 t1 t2;
  assert_norm (lift1' (lift1' (XApp e1 e2) i1 t1) i2 t2 == XApp (lift1' (lift1' e1 i1 t1) i2 t2) (lift1' (lift1' e2 i1 t1) i2 t2) );
  assert_norm ((lift1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) t1) == XApp (lift1' (lift1' e1 i2 t2) (i1 + 1) t1) (lift1' (lift1' e2 i2 t2) (i1 + 1) t1));
  ()

let rec lemma_lift_lift_commute (e: exp 'c 'a) (i1: C.index { i1 <= List.Tot.length 'c }) (i2: C.index { i2 <= i1 }) (t1 t2: Type):
  Lemma (ensures (lift1' (lift1' e i1 t1) i2 t2 === lift1' (lift1' e i2 t2) (i1 + 1) t1))
    (decreases e) =
  C.lemma_lift_lift_commute 'c i1 i2 t1 t2;
  match e with
  | XVal _ -> ()
  | XBVar _ -> ()
  | XVar _ -> ()
  | XApp e1 e2 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2;
    lemma_lift_lift_commute e2 i1 i2 t1 t2;
    lemma_lift_lift_commute_XApp e1 e2 i1 i2 t1 t2
  | XFby v e1 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2
  | XThen e1 e2 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2;
    lemma_lift_lift_commute e2 i1 i2 t1 t2
  | XMu _ e1 ->
    lemma_lift_lift_commute e1 (i1 + 1) (i2 + 1) t1 t2
  | XLet _ e1 e2 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2;
    lemma_lift_lift_commute e2 (i1 + 1) (i2 + 1) t1 t2
  | XCheck _ e1 e2 ->
    lemma_lift_lift_commute e1 i1 i2 t1 t2;
    lemma_lift_lift_commute e2 i1 i2 t1 t2

let rec lemma_subst_lift_id (e: exp 'c 'a) (i: C.index { i <= List.Tot.length 'c }) (t: Type) (p: exp 'c t):
  Lemma (ensures (
    subst1' (lift1' e i t) i p == e))
    (decreases e) =
  match e with
  | XVal _ -> ()
  | XBVar _ -> ()
  | XVar _ -> ()
  | XApp e1 e2 ->
    assert_norm (subst1' (lift1' (XApp e1 e2) i t) i p ==
      XApp (subst1' (lift1' e1 i t) i p) (subst1' (lift1' e2 i t) i p) );
    lemma_subst_lift_id e1 i t p;
    lemma_subst_lift_id e2 i t p
  | XFby v e1 ->
    lemma_subst_lift_id e1 i t p
  | XThen e1 e2 ->
    lemma_subst_lift_id e1 i t p;
    lemma_subst_lift_id e2 i t p
  | XMu _ e1 ->
    lemma_subst_lift_id e1 (i + 1) t (lift1 p 'a)
  | XLet b e1 e2 ->
    lemma_subst_lift_id e1 i t p;
    lemma_subst_lift_id e2 (i + 1) t (lift1 p b)
  | XCheck _ e1 e2 ->
    lemma_subst_lift_id e1 i t p;
    lemma_subst_lift_id e2 i t p

private
let _lift_of_drop (i1: C.index { C.has_index 'c i1 }) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)) (t: Type):
  exp (C.drop1 (t :: 'c) (i1 + 1)) (C.get_index (t :: 'c) (i1 + 1)) =
  lift1 p t

(* Lift distributes over subst:
     lift (e[x' := e']) == (lift e)[S x' := lift e']

   These proofs are a bit involved, so I've split them out into separate lemmas
   for different cases.
*)
let lemma_lift_subst_distribute_le_def (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)): prop =
    C.lemma_lift_drop_commute_le 'c i1 i2 t2;
    lift1' (subst1' e i1 p) i2 t2 == subst1' (lift1' e i2 t2) (i1 + 1) (lift1' p i2 t2)

(* Disabling inversion seems to help solve the actual proof part, but the
   inversion is necessary for the induction / termination proof. So we prove the
   separate lemmas with inversion disabled. *)
#push-options "--fuel 1 --ifuel 0"
private
let lemma_lift_subst_distribute_le_base (e: base_exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  Lemma (ensures (lemma_lift_subst_distribute_le_def e i1 i2 t2 p))
    (decreases e) =
  C.lemma_lift_drop_commute_le 'c i1 i2 t2;
  C.lemma_lift_get_index_gt 'c i1 i2 t2;
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar i -> ()

private
let lemma_lift_subst_distribute_le_XApp (e1: exp 'c ('b -> 'a)) (e2: exp 'c 'b) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  Lemma
    (requires (lemma_lift_subst_distribute_le_def e1 i1 i2 t2 p /\
               lemma_lift_subst_distribute_le_def e2 i1 i2 t2 p))
    (ensures (lemma_lift_subst_distribute_le_def (XApp e1 e2) i1 i2 t2 p)) =
  C.lemma_lift_drop_commute_le 'c i1 i2 t2;
  C.lemma_lift_get_index_gt 'c i1 i2 t2;
  assert_norm (lift1' (subst1' (XApp e1 e2) i1 p) i2 t2 ==
    XApp (lift1' (subst1' e1 i1 p) i2 t2) (lift1' (subst1' e2 i1 p) i2 t2));
  assert_norm (subst1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) (lift1' p i2 t2) ==
    XApp (subst1' (lift1' e1 i2 t2) (i1 + 1) (lift1' p i2 t2)) (subst1' (lift1' e2 i2 t2) (i1 + 1) (lift1' p i2 t2)));
  assert (lift1' (subst1' (XApp e1 e2) i1 p) i2 t2 ==
      subst1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) (lift1' p i2 t2));
  ()

#pop-options


let rec lemma_lift_subst_distribute_le (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  Lemma (ensures (lemma_lift_subst_distribute_le_def e i1 i2 t2 p))
    (decreases e) =
  C.lemma_lift_drop_commute_le 'c i1 i2 t2;
  C.lemma_lift_get_index_gt 'c i1 i2 t2;
  match e with
  | XVal _ | XVar _ | XBVar _ ->
    lemma_lift_subst_distribute_le_base e i1 i2 t2 p
  | XApp e1 e2 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 i1 i2 t2 p;
    lemma_lift_subst_distribute_le_XApp e1 e2 i1 i2 t2 p
  | XFby v e1 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    ()
  | XThen e1 e2 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 i1 i2 t2 p;
    ()
  | XMu _ e1 ->
    C.lemma_lift_drop_commute_le 'c i1 0 'a;
    lemma_lift_lift_commute p i2 0 t2 'a;
    let p' = _lift_of_drop i1 p 'a in
    lemma_lift_subst_distribute_le e1 (i1 + 1) (i2 + 1) t2 p';
    assert (lift1' (subst1' (XMu e1) i1 p) i2 t2 ==
        subst1' (lift1' (XMu e1) i2 t2) (i1 + 1) (lift1' p i2 t2));
    ()

  | XLet b e1 e2 ->
    lemma_lift_lift_commute p i2 0 t2 b;
    let p' = _lift_of_drop i1 p b in

    C.lemma_lift_drop_commute_le 'c i1 i2 t2;

    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 (i1 + 1) (i2 + 1) t2 p';

    assert (lift1' (subst1' (XLet b e1 e2) i1 p) i2 t2 ==
        subst1' (lift1' (XLet b e1 e2) i2 t2) (i1 + 1) (lift1' p i2 t2));
    ()

  | XCheck _ e1 e2 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 i1 i2 t2 p;
    ()

let lemma_subst_subst_distribute_le_def (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)) =
    C.lemma_drop_drop_commute 'c i1 i2;
    C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
    subst1' (subst1' e i1 p1) i2 p2 ==
    subst1' (subst1' e (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)

#push-options "--fuel 1 --ifuel 0"

private
let lemma_subst_subst_distribute_le_base (e: base_exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)):
  Lemma (ensures
    lemma_subst_subst_distribute_le_def e i1 i2 p1 p2) =
  C.lemma_drop_drop_commute 'c i1 i2;
  C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
  match e with
  | XVal v -> ()
  | XVar _ -> ()
  | XBVar i' ->
    if i' = i1
    then ()
    else if i' = i2 + 1
    then begin
      calc (==) {
        C.lift1 (C.drop1 (C.drop1 'c i1) i2) i1 (C.get_index 'c i1);
        (==) { C.lemma_lift_drop_commute_le (C.drop1 'c i1) i2 i1 (C.get_index 'c i1) }
        C.drop1 (C.lift1 (C.drop1 'c i1) i1 (C.get_index 'c i1)) (i2 + 1);
        (==) { C.lemma_lift_drop_eq 'c i1 }
        C.drop1 'c (i2 + 1);
      };
      let p2': exp (C.drop1 'c (i2 + 1)) (C.get_index (C.drop1 'c i1) i2) = coerce_eq () (lift1' p2 i1 (C.get_index 'c i1)) in
      calc (==) {
        subst1' (subst1' e (i2 + 1) p2') i1 (subst1' p1 i2 p2);
        (==) { }
        subst1' (lift1' p2 i1 (C.get_index 'c i1)) i1 (subst1' p1 i2 p2);
        (==) { lemma_subst_lift_id p2 i1 (C.get_index 'c i1) (subst1' p1 i2 p2) }
        p2;
      };
      ()
    end
    else ()

private
let lemma_subst_subst_distribute_le_XApp
  (e1: exp 'c ('b -> 'a)) (e2: exp 'c 'b) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)):
  Lemma
    (requires (lemma_subst_subst_distribute_le_def e1 i1 i2 p1 p2 /\
               lemma_subst_subst_distribute_le_def e2 i1 i2 p1 p2))
    (ensures (lemma_subst_subst_distribute_le_def (XApp e1 e2) i1 i2 p1 p2)) =
  C.lemma_drop_drop_commute 'c i1 i2;
  C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
  assert_norm (subst1' (subst1' (XApp e1 e2) i1 p1) i2 p2 ==
    XApp (subst1' (subst1' e1 i1 p1) i2 p2) (subst1' (subst1' e2 i1 p1) i2 p2));
  assert_norm (subst1' (subst1' (XApp e1 e2) (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2) ==
    XApp (subst1' (subst1' e1 (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)) (subst1' (subst1' e2 (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)));
  ()

private
let lemma_subst_subst_distribute_le_XMu
  {| Pipit.Inhabited.inhabited 'a |}
  (e: exp ('a :: 'c) 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)):
  Lemma
    (requires (lemma_subst_subst_distribute_le_def e (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 'a) (_lift_of_drop i2 p2 'a)))
    (ensures (lemma_subst_subst_distribute_le_def (XMu e) i1 i2 p1 p2)) =
    let p1' = _lift_of_drop i1 p1 'a in
    let p2' = _lift_of_drop i2 p2 'a in
    lemma_lift_lift_commute p2 i1 0 (C.get_index 'c i1) 'a;
    lemma_lift_subst_distribute_le p1 i2 0 'a p2;

    C.lemma_lift_drop_commute_le (C.drop1 'c i1) i2 i1 (C.get_index 'c i1);
    C.lemma_lift_drop_eq 'c i1;

    C.lemma_dropCons 'a 'c (i2 + 2);
    C.lemma_dropCons 'a (C.drop1 'c (i2 + 1)) (i1 + 1);
    assert ('a :: C.drop1 (C.drop1 'c (i2 + 1)) i1 == C.drop1 (C.drop1 ('a :: 'c) (i2 + 2)) (i1 + 1));
    assert (C.get_index ('a :: 'c) (i2 + 2) == C.get_index ('a :: C.drop1 'c i1) (i2 + 1));
    C.lemma_dropCons 'a 'c (i2 + 1);
    C.lemma_dropCons 'a (C.drop1 'c i1) (i2 + 1);
    assert (C.drop1 ('a :: 'c) (i2 + 2) == C.lift1 (C.drop1 ('a :: C.drop1 'c i1) (i2 + 1)) (i1 + 1) (C.get_index 'c i1));

    C.lemma_drop_drop_commute 'c i1 i2;
    C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
    assert (subst1' (subst1' (XMu e) i1 p1) i2 p2 ==
            XMu (subst1' (subst1' e (i1 + 1) p1') (i2 + 1) p2'));
    assert (XMu (coerce_eq () (subst1' (subst1' e (i1 + 1) p1') (i2 + 1) p2')) ==
            XMu #(C.drop1 (C.drop1 'c (i2 + 1)) i1) (subst1' (subst1' e (i2 + 2) (lift1' p2' (i1 + 1) (C.get_index 'c i1))) (i1 + 1) (subst1' p1' (i2 + 1) p2')));
    assert (subst1' (subst1' (XMu e) (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2) ==
            XMu (subst1' (subst1' e (i2 + 2) (lift1 (lift1' p2 i1 (C.get_index 'c i1)) 'a)) (i1 + 1) (lift1 (subst1' p1 i2 p2) 'a)));
    assert (subst1' (subst1' (XMu e) i1 p1) i2 p2 ==
            subst1' (subst1' (XMu e) (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2));

    ()

private
let lemma_subst_subst_distribute_le_XLet
  (e1: exp 'c 'b) (e2: exp ('b :: 'c) 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)):
  Lemma
    (requires (lemma_subst_subst_distribute_le_def e1 i1 i2 p1 p2 /\
               lemma_subst_subst_distribute_le_def e2 (i1 + 1) (i2 + 1) (_lift_of_drop i1 p1 'b) (coerce_eq () (_lift_of_drop i2 p2 'b))))
    (ensures (lemma_subst_subst_distribute_le_def (XLet 'b e1 e2) i1 i2 p1 p2)) =
    let p1' = _lift_of_drop i1 p1 'b in
    let p2' = _lift_of_drop i2 p2 'b in
    lemma_lift_lift_commute p2 i1 0 (C.get_index 'c i1) 'b;
    lemma_lift_subst_distribute_le p1 i2 0 'b p2;

    C.lemma_lift_drop_commute_le (C.drop1 'c i1) i2 i1 (C.get_index 'c i1);
    C.lemma_lift_drop_eq 'c i1;

    C.lemma_dropCons 'b 'c (i2 + 2);
    C.lemma_dropCons 'b (C.drop1 'c (i2 + 1)) (i1 + 1);
    assert ('b :: C.drop1 (C.drop1 'c (i2 + 1)) i1 == C.drop1 (C.drop1 ('b :: 'c) (i2 + 2)) (i1 + 1));
    assert (C.get_index ('b :: 'c) (i2 + 2) == C.get_index ('b :: C.drop1 'c i1) (i2 + 1));
    C.lemma_dropCons 'b 'c (i2 + 1);
    C.lemma_dropCons 'b (C.drop1 'c i1) (i2 + 1);
    assert (C.drop1 ('b :: 'c) (i2 + 2) == C.lift1 (C.drop1 ('b :: C.drop1 'c i1) (i2 + 1)) (i1 + 1) (C.get_index 'c i1));

    C.lemma_drop_drop_commute 'c i1 i2;
    C.lemma_drop_get_index_lt 'c (i2 + 1) i1;

    let e1'l = subst1' (subst1' e1 i1 p1) i2 p2 in
    let e2'l = subst1' (subst1' e2 (i1 + 1) p1') (i2 + 1) p2' in

    assert (subst1' (subst1' (XLet 'b e1 e2) i1 p1) i2 p2 ==
            XLet 'b e1'l e2'l);
    assert (XLet 'b e1'l e2'l ==
            XLet #(C.drop1 (C.drop1 'c (i2 + 1)) i1) 'b e1'l (subst1' (subst1' e2 (i2 + 2) (lift1' p2' (i1 + 1) (C.get_index 'c i1))) (i1 + 1) (subst1' p1' (i2 + 1) p2')));
    assert (subst1' (subst1' (XLet 'b e1 e2) (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2) ==
            XLet 'b (subst1' (subst1' e1 (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)) (subst1' (subst1' e2 (i2 + 2) (lift1 (lift1' p2 i1 (C.get_index 'c i1)) 'b)) (i1 + 1) (lift1 (subst1' p1 i2 p2) 'b)));
    assert (subst1' (subst1' (XLet 'b e1 e2) i1 p1) i2 p2 ==
            subst1' (subst1' (XLet 'b e1 e2) (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2));

    ()

#push-options "--fuel 1 --ifuel 1"

let rec lemma_subst_subst_distribute_le (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)):
  Lemma (ensures
    (C.lemma_drop_drop_commute 'c i1 i2;
    C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
    subst1' (subst1' e i1 p1) i2 p2 ==
    subst1' (subst1' e (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)))
    (decreases e) =
  C.lemma_drop_drop_commute 'c i1 i2;
  C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
  match e with
  | XVal _ | XVar _ | XBVar _ -> lemma_subst_subst_distribute_le_base e i1 i2 p1 p2

  | XApp e1 e2 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2;
    lemma_subst_subst_distribute_le e2 i1 i2 p1 p2;
    lemma_subst_subst_distribute_le_XApp e1 e2 i1 i2 p1 p2
  | XFby v e1 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2;
    ()
  | XThen e1 e2 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2;
    lemma_subst_subst_distribute_le e2 i1 i2 p1 p2;
    ()
  | XCheck _ e1 e2 ->
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2;
    lemma_subst_subst_distribute_le e2 i1 i2 p1 p2;
    ()

  | XMu _ e1 ->
    let p1' = _lift_of_drop i1 p1 'a in
    let p2' = _lift_of_drop i2 p2 'a in
    lemma_subst_subst_distribute_le e1 (i1 + 1) (i2 + 1) p1' p2';
    lemma_subst_subst_distribute_le_XMu e1 i1 i2 p1 p2
  | XLet b e1 e2 ->
    let p1' = _lift_of_drop i1 p1 b in
    let p2' = _lift_of_drop i2 p2 b in
    lemma_subst_subst_distribute_le e1 i1 i2 p1 p2;
    lemma_subst_subst_distribute_le e2 (i1 + 1) (i2 + 1) p1' p2';
    lemma_subst_subst_distribute_le_XLet e1 e2 i1 i2 p1 p2

let lemma_subst_subst_distribute_XMu {| Pipit.Inhabited.inhabited 'a |} (e: exp ('a :: 'c) 'a) (i: C.index { C.has_index 'c i }) (p: exp (C.drop1 'c i) (C.get_index 'c i)):
  Lemma (ensures
    subst1' (subst1 e (XMu e)) i p ==
    subst1 (subst1' e (i + 1) (lift1 p 'a)) (XMu (subst1' e (i + 1) (lift1 p 'a))))
    =
  lemma_subst_subst_distribute_le e 0 i (XMu e) p
