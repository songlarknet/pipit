(* Manipulating bindings: opening, closing, substituting and lifting *)
module Pipit.Exp.Binding

open Pipit.Exp.Base
module C = Pipit.Context

(* Open an expression so that a bound variable becomes free.
   Not currently used. *)
let rec open1' (#c: C.context) (e: exp c 'a) (n: C.index { C.has_index c n }) (x: C.var (C.get_index c n)): Tot (exp (C.open1' c n) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    if i = n
    then
      XVar x
    else
      (C.lemma_open_preserves_opt_index c n i;
      XBVar (C.index_drop i n 1))
  | XVar x' ->
    XVar x'
  | XApp f e -> XApp (open1' f n x) (open1' e n x)
  | XFby v e -> XFby v (open1' e n x)
  | XThen e1 e2 -> XThen (open1' e1 n x) (open1' e2 n x)
  | XMu _ e -> XMu (open1' e (n + 1) x)
  | XLet b e1 e2 ->
    let e1' = open1' e1 n x in
    let e2' = open1' e2 (n + 1) x in
    XLet b e1' e2'
  | XCheck name e1 e2 -> XCheck name (open1' e1 n x) (open1' e2 n x)

let open1 (e: exp 'c 'a { C.has_index 'c 0 }) x = open1' e 0 x

(* Close an expression so that a free variable becomes bound.
   This is used by the syntactic sugar, but not in the semantics. *)
let rec close1' (#c: C.context) (e: exp c 'a) (x: C.var 'b) (n: C.index { n <= List.Tot.length c }): Tot (exp (C.close1' c 'b n) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    C.lemma_close_preserves_opt_index c 'b n i;
    XBVar (C.index_lift i n 1)
  | XVar x' ->
    if C.var_eq x x'
    then
      (C.lemma_close_contains c 'b n;
      XBVar n)
    else
      XVar x'
  | XApp f e -> XApp (close1' f x n) (close1' e x n)
  | XFby v e -> XFby v (close1' e x n)
  | XThen e1 e2 -> XThen (close1' e1 x n) (close1' e2 x n)
  | XMu _ e -> XMu (close1' e x (n + 1))
  | XLet b e1 e2 -> XLet b (close1' e1 x n) (close1' e2 x (n + 1))
  | XCheck name e1 e2 -> XCheck name (close1' e1 x n) (close1' e2 x n)

let close1 (e: exp 'c 'a) x = close1' e x 0

(* Lift an expression by incrementing bound variable indices at or above n.
   This is used directly by substitution, so we need to prove some properties
   about it. Could we implement this in terms of close1' with a dummy free
   variable? *)
let rec lift1' (#c: C.context) (e: exp c 'a) (n: C.index { n <= List.Tot.length c }) (t: Type): Tot (exp (C.lift1 c n t) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    C.lemma_close_preserves_opt_index c t n i;
    XBVar (C.index_lift i n 1)
  | XVar x' ->
    XVar x'
  | XApp f e -> XApp (lift1' f n t) (lift1' e n t)
  | XFby v e -> XFby v (lift1' e n t)
  | XThen e1 e2 -> XThen (lift1' e1 n t) (lift1' e2 n t)
  | XMu _ e1 ->
    let e1': exp (C.lift1 (C.lift1 c 0 'a) (n + 1) t) 'a = lift1' e1 (n + 1) t in
    let e1'': exp (C.lift1 (C.lift1 c n t) 0 'a) 'a = e1' in
    XMu e1''
  | XLet b e1 e2 -> XLet b (lift1' e1 n t) (lift1' e2 (n + 1) t)
  | XCheck name e1 e2 -> XCheck name (lift1' e1 n t) (lift1' e2 n t)

let lift1 (#c: C.context) (e: exp c 'a) (t: Type): exp (C.lift1 c 0 t) 'a =
  lift1' e 0 t

(* Substitute one bound variable for a bound expression.
   This is used by the semantics, so we need to prove that it commutes. *)
let rec subst1' (#c: C.context) (e: exp c 'a) (i: C.index { C.has_index c i }) (payload: exp (C.drop1 c i) (C.get_index c i)): Tot (exp (C.drop1 c i) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i' ->
    if i' = i
    then payload
    else
      (C.lemma_open_preserves_opt_index c i i';
      XBVar (C.index_drop i' i 1))
  | XVar x' -> XVar x'
  | XApp f e -> XApp (subst1' f i payload) (subst1' e i payload)
  | XFby v e -> XFby v (subst1' e i payload)
  | XThen e1 e2 -> XThen (subst1' e1 i payload) (subst1' e2 i payload)
  | XMu _ e1 ->
    let e1': exp (C.drop1 (C.lift1 c 0 'a) (i + 1)) 'a = subst1' e1 (i + 1) (lift1 payload 'a) in
    let e1'': exp (C.lift1 (C.drop1 c i) 0 'a) 'a = e1' in
    XMu e1''
  | XLet b e1 e2 -> XLet b (subst1' e1 i payload) (subst1' e2 (i + 1) (lift1 payload b))
  | XCheck name e1 e2 -> XCheck name (subst1' e1 i payload) (subst1' e2 i payload)

let subst1 (#c: C.context { C.has_index c 0 }) (e: exp c 'a) (payload: exp (C.drop1 c 0) (C.get_index c 0)): Tot (exp (C.drop1 c 0) 'a) (decreases e) =
  subst1' e 0 payload

#push-options "--split_queries always"

private
let lemma_lift_lift_commute_XApp (e1: exp 'c ('b -> 'a)) (e2: exp 'c 'b) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t1 t2: Type):
  Lemma
    (requires (lift1' (lift1' e1 i1 t1) i2 t2 === lift1' (lift1' e1 i2 t2) (i1 + 1) t1) /\
              (lift1' (lift1' e2 i1 t1) i2 t2 === lift1' (lift1' e2 i2 t2) (i1 + 1) t1))
    (ensures (lift1' (lift1' (XApp e1 e2) i1 t1) i2 t2 === lift1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) t1))
     =
  C.lemma_lift_lift_commute 'c i1 i2 t1 t2;
  // calc (==) {
  //  (lift1' (XApp e1 e2) i1 t1);
  //  == { () }
  //  XApp (lift1' e1 i1 t1) (lift1' e2 i1 t1);
  // };
 //  assert ((lift1' (XApp e1 e2) i1 t1) == XApp (lift1' e1 i1 t1) (lift1' e2 i1 t1)) by (FStar.Tactics.norm [delta; primops; iota; nbe; zeta]; FStar.Tactics.dump "ok");
  assert_norm ((lift1' (XApp e1 e2) i1 t1) == XApp (lift1' e1 i1 t1) (lift1' e2 i1 t1));
  assert_norm (lift1' (XApp (lift1' e1 i1 t1) (lift1' e2 i1 t1)) i2 t2 == XApp (lift1' (lift1' e1 i1 t1) i2 t2) (lift1' (lift1' e2 i1 t1) i2 t2) );
  assert (XApp (lift1' (lift1' e1 i1 t1) i2 t2) (lift1' (lift1' e2 i1 t1) i2 t2) == XApp (lift1' (lift1' e1 i2 t2) (i1 + 1) t1) (lift1' (lift1' e2 i2 t2) (i1 + 1) t1));
  assert_norm ((lift1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) t1) == XApp (lift1' (lift1' e1 i2 t2) (i1 + 1) t1) (lift1' (lift1' e2 i2 t2) (i1 + 1) t1));
  // assert (
  //   lift1' (lift1' (XApp e1 e2) i2 t2) (i1 + 1) t1) by (FStar.Tactics.norm [delta; primops; iota; nbe]; FStar.Tactics.dump "ok");
  ()

let rec lemma_lift_lift_commute (e: exp 'c 'a) (i1: C.index { C.has_index 'c i1 }) (i2: C.index { i2 <= i1 }) (t1 t2: Type):
  Lemma (ensures (lift1' (lift1' e i1 t1) i2 t2 === lift1' (lift1' e i2 t2) (i1 + 1) t1))
  // Lemma (ensures (C.lemma_lift_lift_commute 'c i1 i2 t1 t2;
  //   lift1' (lift1' e i1 t1) i2 t2 == lift1' (lift1' e i2 t2) (i1 + 1) t1))
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

let rec subst_lift_id (e: exp 'c 'a) (i: C.index { C.has_index 'c i }) (p: exp 'c (C.get_index 'c i)) (t: Type):
  Lemma (ensures subst1' (lift1' e i t) i p === e) =
  C.lemma_drop_lift_eq 'c i t;
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | _ -> admit ()
  // | XPrim2 _ e1 e2 ->
  //   subst_lift_id e1 p x;
  //   subst_lift_id e2 p x
  // | XIte ep e1 e2 ->
  //   subst_lift_id ep p x;
  //   subst_lift_id e1 p x;
  //   subst_lift_id e2 p x
  // | XFby _ e1 -> subst_lift_id e1 p x
  // | XThen e1 e2 ->
  //   subst_lift_id e1 p x;
  //   subst_lift_id e2 p x
  // | XMu e1 ->
  //   subst_lift_id e1 (lift p 0) (x + 1)
  // | XLet b e1 e2 ->
  //   subst_lift_id e1 p x;
  //   subst_lift_id e2 (lift p 0) (x + 1)

(*
let rec lift_subst_distribute_le (e p: exp) (x1: var) (x2: var { x2 <= x1 }):
  Lemma (ensures lift (subst e x1 p) x2 == subst (lift e x2) (x1 + 1) (lift p x2)) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 _ e1 e2 ->
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 p x1 x2
  | XIte ep e1 e2 ->
    lift_subst_distribute_le ep p x1 x2;
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 p x1 x2
  | XPre e1 -> lift_subst_distribute_le e1 p x1 x2
  | XThen e1 e2 ->
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 p x1 x2
  | XMu e1 ->
    lift_subst_distribute_le e1 (lift p 0) (x1 + 1) (x2 + 1);
    lemma_lift_lift_commute p x2 0
  | XLet e1 e2 ->
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 (lift p 0) (x1 + 1) (x2 + 1);
    lemma_lift_lift_commute p x2 0

let rec subst_subst_distribute_le (e p1 p2: exp) (x1: var) (x2: var { x1 <= x2 }):
  Lemma (ensures subst (subst e x1 p1) x2 p2 ==
                 subst (subst e (x2 + 1) (lift p2 x1)) x1 (subst p1 x2 p2)) =
  match e with
  | XVal _ -> ()
  | XVar x' ->
    if x' = x2 + 1
    then subst_lift_id p2 (subst p1 x2 p2) x1
  | XPrim2 _ e1 e2 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2;
    subst_subst_distribute_le e2 p1 p2 x1 x2
  | XIte ep e1 e2 ->
    subst_subst_distribute_le ep p1 p2 x1 x2;
    subst_subst_distribute_le e1 p1 p2 x1 x2;
    subst_subst_distribute_le e2 p1 p2 x1 x2
  | XPre e1 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2
  | XThen e1 e2 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2;
    subst_subst_distribute_le e2 p1 p2 x1 x2
  | XMu e1 ->
    subst_subst_distribute_le e1 (lift p1 0) (lift p2 0) (x1 + 1) (x2 + 1);
    lemma_lift_lift_commute p2 x1 0;
    lift_subst_distribute_le p1 p2 x2 0
  | XLet e1 e2 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2;
    subst_subst_distribute_le e2 (lift p1 0) (lift p2 0) (x1 + 1) (x2 + 1);
    lemma_lift_lift_commute p2 x1 0;
    lift_subst_distribute_le p1 p2 x2 0

let subst_subst_distribute_XMu (e p: exp) (x: var):
  Lemma (ensures subst (subst e 0 (XMu e)) x p ==
                 subst (subst e (x + 1) (lift p 0)) 0 (XMu (subst e (x + 1) (lift p 0)))) =
 subst_subst_distribute_le e (XMu e) p 0 x

*)
