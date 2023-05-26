(* Manipulating bindings: opening, closing, substituting and lifting *)
module Pipit.Exp.Binding.Properties

open Pipit.Exp.Base
open Pipit.Exp.Binding

module C = Pipit.Context

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

private
let _lift_subst_e (e_sub: exp ('b :: 'c) 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  (exp ('b :: C.lift1 (C.drop1 'c i1) i2 t2) 'a) =
    (lift1' (subst1' e_sub (i1 + 1) (_lift_of_drop i1 p 'b)) (i2 + 1) t2)

private
let _subst_lift_e (e_sub: exp ('b :: 'c) 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  (exp ('b :: C.drop1 (C.lift1 'c i2 t2) (i1 + 1)) 'a) =
    let ll: exp (C.lift1 ('b :: C.drop1 'c i1) (i2 + 1) t2) (C.get_index 'c i1) =
      lift1' (lift1 p 'b) (i2 + 1) t2 in
    C.lemma_liftCons 'b (C.drop1 'c i1) (i2 + 1) t2;
    C.lemma_lift_drop_commute_le 'c i1 i2 t2;
    C.lemma_lift_get_index 'c i1 0 'b;
    C.lemma_lift_get_index ('b :: 'c) (i1 + 1) (i2 + 1) t2;
    let ll: exp ('b :: C.drop1 (C.lift1 'c i2 t2) (i1 + 1)) (C.get_index (C.lift1 ('b :: 'c) (i2 + 1) t2) (i1 + 2)) =
      ll in
    (subst1' (lift1' e_sub (i2 + 1) t2) ((i1 + 1) + 1) ll)

let lemma_lift1_XMu {| Pipit.Inhabited.inhabited 'a |} (e: exp ('a :: 'c) 'a) (n: C.index { n <= List.Tot.length 'c }) (t: Type):
  Lemma (ensures (
    lift1' (XMu e) n t == XMu (lift1' e (n + 1) t))) =
    ()

let lemma_subst1_XMu {| Pipit.Inhabited.inhabited 'a |} (e: exp ('a :: 'c) 'a) (n: C.index { n < List.Tot.length 'c }) (p: exp (C.drop1 'c n) (C.get_index 'c n)):
  Lemma (ensures (
    subst1' (XMu e) n p == XMu (subst1' e (n + 1) (lift1 p 'a)))) =
    ()

#push-options "--fuel 1 --ifuel 0"
private
let lemma_lift_subst_distribute_le_XBVar (i: C.index { C.has_index 'c i }) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  Lemma (ensures (
    let e: exp 'c (C.get_index 'c i) = XBVar i in
    C.lemma_lift_drop_commute_le 'c i1 i2 t2;
    lift1' (subst1' e i1 p) i2 t2 == subst1' (lift1' e i2 t2) (i1 + 1) (coerce_eq () (lift1' p i2 t2))))
    =
  C.lemma_lift_drop_commute_le 'c i1 i2 t2;
  ()
#pop-options

let rec lemma_lift_subst_distribute_le (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t2: Type) (p: exp (C.drop1 'c i1) (C.get_index 'c i1)):
  Lemma (ensures (
    C.lemma_lift_drop_commute_le 'c i1 i2 t2;
    lift1' (subst1' e i1 p) i2 t2 == subst1' (lift1' e i2 t2) (i1 + 1) (lift1' p i2 t2)))
    (decreases e) =
  C.lemma_lift_drop_commute_le 'c i1 i2 t2;
  C.lemma_lift_get_index_gt 'c i1 i2 t2;
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XBVar i ->
    lemma_lift_subst_distribute_le_XBVar i i1 i2 t2 p
  | XApp e1 e2 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 i1 i2 t2 p;
    assert_norm (lift1' (subst1' (XApp e1 e2) i1 p) i2 t2 ==
      XApp (lift1' (subst1' e1 i1 p) i2 t2) (lift1' (subst1' e2 i1 p) i2 t2));
    assert_norm (subst1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) (lift1' p i2 t2) ==
      XApp (subst1' (lift1' e1 i2 t2) (i1 + 1) (lift1' p i2 t2)) (subst1' (lift1' e2 i2 t2) (i1 + 1) (lift1' p i2 t2)));
    ()
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
    admit ()

  | XLet b e1 e2 ->
    lemma_lift_lift_commute p i2 0 t2 b;
    let p' = _lift_of_drop i1 p b in

    C.lemma_lift_drop_commute_le 'c i1 i2 t2;

    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 (i1 + 1) (i2 + 1) t2 p';

    admit ()

  | XCheck _ e1 e2 ->
    lemma_lift_subst_distribute_le e1 i1 i2 t2 p;
    lemma_lift_subst_distribute_le e2 i1 i2 t2 p;
    ()

let lemma_subst_subst_distribute_le_def (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i1 <= i2 /\ i2 < List.Tot.length 'c - 1 }) (p1: exp (C.drop1 'c i1) (C.get_index 'c i1)) (p2: exp (C.drop1 (C.drop1 'c i1) i2) (C.get_index (C.drop1 'c i1) i2)) =
    C.lemma_drop_drop_commute 'c i1 i2;
    C.lemma_drop_get_index_lt 'c (i2 + 1) i1;
    subst1' (subst1' e i1 p1) i2 p2 ==
    subst1' (subst1' e (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)

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
let lemma_subst_XMu_unfold
  {| Pipit.Inhabited.inhabited 'a |}
  (e: exp ('a :: 'c) 'a) (i: C.index { C.has_index 'c i }) (p: exp (C.drop1 'c i) (C.get_index 'c i)):
  Lemma (subst1' (XMu e) i p == XMu (subst1' e (i + 1) (lift1 p 'a))) = ()

// #pop-options
#push-options "--fuel 1 --ifuel 1"

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

    assert (C.get_index ('a :: 'c) (i1 + 1) == C.get_index 'c i1);

    C.lemma_dropCons 'a 'c (i2 + 2);
    C.lemma_dropCons 'a (C.drop1 'c (i2 + 1)) (i1 + 1);
    assert ('a :: C.drop1 (C.drop1 'c (i2 + 1)) i1 == C.drop1 (C.drop1 ('a :: 'c) (i2 + 2)) (i1 + 1));
    assume (C.get_index ('a :: 'c) (i2 + 2) == C.get_index ('a :: C.drop1 'c i1) (i2 + 1));
    // assert (C.get_index ('a :: 'c) (i2 + 2) == C.get_index ('a :: C.drop1 'c i1) (i2 + 1));
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

    assert (C.get_index ('b :: 'c) (i1 + 1) == C.get_index 'c i1);

    C.lemma_dropCons 'b 'c (i2 + 2);
    C.lemma_dropCons 'b (C.drop1 'c (i2 + 1)) (i1 + 1);
    assert ('b :: C.drop1 (C.drop1 'c (i2 + 1)) i1 == C.drop1 (C.drop1 ('b :: 'c) (i2 + 2)) (i1 + 1));
    assume (C.get_index ('b :: 'c) (i2 + 2) == C.get_index ('b :: C.drop1 'c i1) (i2 + 1));
    // assert (C.get_index ('b :: 'c) (i2 + 2) == C.get_index ('b :: C.drop1 'c i1) (i2 + 1));
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
    assert_norm (subst1' (subst1' (XApp e1 e2) i1 p1) i2 p2 ==
      XApp (subst1' (subst1' e1 i1 p1) i2 p2) (subst1' (subst1' e2 i1 p1) i2 p2));
    assert_norm (subst1' (subst1' (XApp e1 e2) (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2) ==
      XApp (subst1' (subst1' e1 (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)) (subst1' (subst1' e2 (i2 + 1) (lift1' p2 i1 (C.get_index 'c i1))) i1 (subst1' p1 i2 p2)));
    ()
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
