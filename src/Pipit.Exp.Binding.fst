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
    XMu (lift1' e1 (n + 1) t)
  | XLet b e1 e2 -> XLet b (lift1' e1 n t) (lift1' e2 (n + 1) t)
  | XCheck name e1 e2 -> XCheck name (lift1' e1 n t) (lift1' e2 n t)

let lift1 (#c: C.context) (e: exp c 'a) (t: Type): exp (t :: c) 'a =
  lift1' e 0 t

let lift_under (#c: C.context) (e: exp ('a :: c) 'a) (n: C.index { n <= List.Tot.length c }) (t: Type): exp ('a :: C.lift1 c n t) 'a =
  lift1' e (n + 1) t

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
    XMu (subst1' e1 (i + 1) (lift1 payload 'a))
  | XLet b e1 e2 -> XLet b (subst1' e1 i payload) (subst1' e2 (i + 1) (lift1 payload b))
  | XCheck name e1 e2 -> XCheck name (subst1' e1 i payload) (subst1' e2 i payload)

let subst1 (#c: C.context { C.has_index c 0 }) (e: exp c 'a) (payload: exp (C.drop1 c 0) (C.get_index c 0)): Tot (exp (List.Tot.tl c) 'a) (decreases e) =
  subst1' e 0 payload