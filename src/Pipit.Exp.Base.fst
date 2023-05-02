module Pipit.Exp.Base
module C = Pipit.Context
open Pipit.Inhabited

(* TODO: restrict "properties" to booleans for now to avoid universe stuff *)
type xprop = bool

noeq
type exp (c: C.context) 'a =
  // v
  | XVal   : 'a -> exp c 'a
  // bound variable (de Bruijn index)
  | XBVar  : (i: C.index { C.opt_index c i == Some 'a }) -> exp c 'a
  // free variables
  | XVar   : (x: C.var 'a) -> exp c 'a
  // f(e,...)
  | XApp   : exp c ('b -> 'a) -> exp c 'b -> exp c 'a
  // v fby e
  | XFby   : 'a -> exp c 'a -> exp c 'a
  // e -> e'
  | XThen  : exp c 'a -> exp c 'a -> exp c 'a
  // µx. e[x]
  | XMu    : {| inhabited 'a |} -> exp ('a :: c) 'a -> exp c 'a
  // let x = e in e[x]
  | XLet   : (b: Type) -> exp c b -> exp (b :: c) 'a -> exp c 'a

  // Proof terms
  // Contracts for hiding implementation:
  //   (λx. { assumes } body { λr. guarantees })(arg)
  // TODO: assumes and guarantees should probably be in context c, so they can be CSEd with the main expression. body should be separate to allow separate codegen
  | XContract:
           (assumes: exp ['b] xprop) ->
           (guarantees: exp ['a; 'b] xprop) ->
           (body: exp ['b] 'a) ->
           (arg: exp c 'b) ->
           exp c 'a
  // check "" e in e
  | XCheck : string -> exp c xprop -> exp c 'a -> exp c 'a

let rec open1' (#c: C.context) (e: exp c 'a) (n: C.index { C.has_index c n }) (x: C.var (C.get_index c n)): Tot (exp (C.open1' c n) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    if i = n
    then
      XVar x
    else
      (C.open_preserves_opt_index_lemma c n i;
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
  | XContract a g b arg  ->
    XContract a g b (open1' arg n x)
  | XCheck name e1 e2 -> XCheck name (open1' e1 n x) (open1' e2 n x)

let rec close1' (#c: C.context) (e: exp c 'a) (x: C.var 'b) (n: C.index { n <= List.Tot.length c }): Tot (exp (C.close1' c 'b n) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    C.close_preserves_opt_index_lemma c 'b n i;
    XBVar (C.index_lift i n 1)
  | XVar x' ->
    if C.Var?.v x = C.Var?.v x'
    then
      (C.cheat_variables_assume_global x x';
      C.close_contains_lemma c 'b n;
      XBVar n)
    else
      (// C.close_preserves_opt_var_lemma c x n x';
      XVar x')
  | XApp f e -> XApp (close1' f x n) (close1' e x n)
  | XFby v e -> XFby v (close1' e x n)
  | XThen e1 e2 -> XThen (close1' e1 x n) (close1' e2 x n)
  | XMu _ e -> XMu (close1' e x (n + 1))
  | XLet b e1 e2 -> XLet b (close1' e1 x n) (close1' e2 x (n + 1))
  | XContract a g b arg -> XContract a g b (close1' arg x n)
  | XCheck name e1 e2 -> XCheck name (close1' e1 x n) (close1' e2 x n)

let open1 (e: exp 'c 'a { C.has_index 'c 0 }) x = open1' e 0 x
let close1 (e: exp 'c 'a) x = close1' e x 0

let rec lift1' (#c: C.context) (e: exp c 'a) (n: C.index { n <= List.Tot.length c }) (t: Type): Tot (exp (C.lift1 c n t) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    // C.bind_index_preserves_opt_index_lemma c n i t;
    C.close_preserves_opt_index_lemma c t n i;
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
  | XContract a g b arg ->
    XContract a g b (lift1' arg n t)
  | XCheck name e1 e2 -> XCheck name (lift1' e1 n t) (lift1' e2 n t)

let lift1 (#c: C.context) (e: exp c 'a) (t: Type): exp (C.lift1 c 0 t) 'a =
  lift1' e 0 t

let rec subst_index1' (#c: C.context) (e: exp c 'a) (i: C.index { C.has_index c i }) (payload: exp (C.drop1 c i) (C.get_index c i)): Tot (exp (C.drop1 c i) 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i' ->
    if i' = i
    then payload
    else
      (C.open_preserves_opt_index_lemma c i i';
      XBVar (C.index_drop i' i 1))
  | XVar x' -> XVar x'
  | XApp f e -> XApp (subst_index1' f i payload) (subst_index1' e i payload)
  | XFby v e -> XFby v (subst_index1' e i payload)
  | XThen e1 e2 -> XThen (subst_index1' e1 i payload) (subst_index1' e2 i payload)
  | XMu _ e1 ->
    let e1': exp (C.drop1 (C.lift1 c 0 'a) (i + 1)) 'a = subst_index1' e1 (i + 1) (lift1 payload 'a) in
    let e1'': exp (C.lift1 (C.drop1 c i) 0 'a) 'a = e1' in
    XMu e1''
  | XLet b e1 e2 -> XLet b (subst_index1' e1 i payload) (subst_index1' e2 (i + 1) (lift1 payload b))
  | XContract a g b arg ->
    XContract a g b (subst_index1' arg i payload)
  | XCheck name e1 e2 -> XCheck name (subst_index1' e1 i payload) (subst_index1' e2 i payload)

let subst_index1 (#c: C.context { C.has_index c 0 }) (e: exp c 'a) (payload: exp (C.drop1 c 0) (C.get_index c 0)): Tot (exp (C.drop1 c 0) 'a) (decreases e) =
  subst_index1' e 0 payload

let rec weaken (#c c': C.context) (e: exp c 'a): Tot (exp (C.append c c') 'a) (decreases e) =
  match e with
  | XVal v -> XVal v
  | XBVar i' ->
    C.append_preserves_opt_index_lemma c c' i';
    XBVar i'
  | XVar x' -> XVar x'
  | XApp f e -> XApp (weaken c' f) (weaken c' e)
  | XFby v e -> XFby v (weaken c' e)
  | XThen e1 e2 -> XThen (weaken c' e1) (weaken c' e2)
  | XMu _ e1 ->
    let e1': exp (C.append (C.lift1 c 0 'a) c') 'a = weaken c' e1 in
    let e1'': exp (C.lift1 (C.append c c') 0 'a) 'a = e1' in
    XMu e1''
  | XLet b e1 e2 -> XLet b (weaken c' e1) (weaken c' e2)
  | XContract a g b arg ->
    XContract a g b (weaken c' arg)
  | XCheck name e1 e2 -> XCheck name (weaken c' e1) (weaken c' e2)
