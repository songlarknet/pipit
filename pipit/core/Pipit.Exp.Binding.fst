(* Manipulating bindings: opening, closing, substituting and lifting.
   Properties about these functions are in `Pipit.Exp.Binding.Properties`. *)
module Pipit.Exp.Binding

open Pipit.Prim.Table
open Pipit.Exp.Base

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties

(* Close an expression so that a free variable becomes bound.
   This is used by the syntactic sugar, but not in the semantics. *)
let close1_base' (#a #b: ('t).ty) (#c: context 't) (e: exp_base 't c a) (x: C.var b) (n: C.index_insert c): Tot (exp_base 't (C.close1' c b n) a) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    XBVar (C.index_lift i n)
  | XVar x' ->
    if ('t).var_eq x x'
    then
      XBVar n
    else
      XVar x'

let rec close1' (#a #b: ('t).ty) (#c: context 't) (e: exp 't c a) (x: C.var b) (n: C.index_insert c): Tot (exp 't (C.close1' c b n) a) (decreases e) =
  match e with
  | XBase e1 -> XBase (close1_base' e1 x n)
  | XApps e1 -> XApps (close1_apps' e1 x n)
  | XFby v e -> XFby v (close1' e x n)
  | XMu e -> XMu (close1' e x (n + 1))
  | XLet b e1 e2 -> XLet b (close1' e1 x n) (close1' e2 x (n + 1))
  | XContract ps r g i -> XContract ps (close1' r x n) (close1' g x (n + 1)) (close1' i x n)
  | XCheck name e1 -> XCheck name (close1' e1 x n)
and close1_apps' (#a: funty ('t).ty) (#b: ('t).ty) (#c: context 't) (e: exp_apps 't c a) (x: C.var b) (n: C.index_insert c): Tot (exp_apps 't (C.close1' c b n) a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f e -> XApp (close1_apps' f x n) (close1' e x n)

let close1_bind' (#a #bind #b: ('t).ty) (#c: context 't) (e': exp_bind 't bind c a) (x: C.var b) (n: C.index_insert c): Tot (exp_bind 't bind (C.close1' c b n) a) =
  close1' e' x (n + 1)

let close1 (#a #b: ('t).ty) (#c: context 't) (e: exp 't c a) (x: C.var b): exp 't (b :: c) a = close1' e x 0

(* Lift an expression by incrementing bound variable indices at or above n.
   This is used directly by substitution, so we need to prove some properties
   about it. Could we implement this in terms of close1' with a dummy free
   variable? *)
let lift1_base' (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (n: C.index_insert c) (t: ('t).ty): Tot (exp_base 't (C.lift1 c n t) a) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    XBVar (C.index_lift i n)
  | XVar x' ->
    XVar x'

let rec lift1' (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (n: C.index_insert c) (t: ('t).ty): Tot (exp 't (C.lift1 c n t) a) (decreases e) =
  match e with
  | XBase e1 -> XBase (lift1_base' e1 n t)
  | XApps e1 -> XApps (lift1_apps' e1 n t)
  | XFby v e -> XFby v (lift1' e n t)
  | XMu e1 ->
    XMu (lift1' e1 (n + 1) t)
  | XLet b e1 e2 -> XLet b (lift1' e1 n t) (lift1' e2 (n + 1) t)
  | XContract ps r g i -> XContract ps (lift1' r n t) (lift1' g (n + 1) t) (lift1' i n t)
  | XCheck name e1 -> XCheck name (lift1' e1 n t)
and lift1_apps' (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (n: C.index_insert c) (t: ('t).ty): Tot (exp_apps 't (C.lift1 c n t) a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f e -> XApp (lift1_apps' f n t) (lift1' e n t)

unfold
let lift1_bind' (#a #b: ('t).ty) (#c: context 't) (e: exp_bind 't b c a) (n: C.index_insert c) (t: ('t).ty): Tot (exp_bind 't b (C.lift1 c n t) a) =
  lift1' e (n + 1) t

unfold
let lift1 (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (t: ('t).ty): exp 't (t :: c) a =
  lift1' e 0 t

(* Substitute one bound variable for a bound expression.
   This is used by the semantics, so we need to prove that it commutes. *)
let subst1_base' (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (i: C.index { C.has_index c i }) (payload: exp 't (C.drop1 c i) (C.get_index c i)): Tot (exp 't (C.drop1 c i) a) =
  match e with
  | XVal v -> XBase (XVal v)
  | XBVar i' ->
    if i' = i
    then payload
    else XBase (XBVar (C.index_drop i' i))
  | XVar x' -> XBase (XVar x')


let rec subst1' (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (i: C.index { C.has_index c i }) (payload: exp 't (C.drop1 c i) (C.get_index c i)): Tot (exp 't (C.drop1 c i) a) (decreases e) =
  match e with
  | XBase e1 -> subst1_base' e1 i payload
  | XApps e1 -> XApps (subst1_apps' e1 i payload)
  | XFby v e -> XFby v (subst1' e i payload)
  | XMu e1 ->
    XMu (subst1' e1 (i + 1) (lift1 payload a))
  | XLet b e1 e2 -> XLet b (subst1' e1 i payload) (subst1' e2 (i + 1) (lift1 payload b))
  | XContract ps r g impl -> XContract ps (subst1' r i payload) (subst1' g (i + 1) (lift1 payload a)) (subst1' impl i payload)
  | XCheck name e1 -> XCheck name (subst1' e1 i payload)
and subst1_apps' (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (i: C.index { C.has_index c i }) (payload: exp 't (C.drop1 c i) (C.get_index c i)): Tot (exp_apps 't (C.drop1 c i) a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f e -> XApp (subst1_apps' f i payload) (subst1' e i payload)

unfold
let subst1_bind' (#a #b: ('t).ty) (#c: context 't) (e: exp_bind 't b c a) (i: C.index { C.has_index c i }) (payload: exp 't (C.drop1 c i) (C.get_index c i)): Tot (exp_bind 't b (C.drop1 c i) a) =
  subst1' e (i + 1) (lift1 payload b)

unfold
let subst1 (#a: ('t).ty) (#c: context 't { C.has_index c 0 }) (e: exp 't c a) (payload: exp 't (C.drop1 c 0) (C.get_index c 0)): Tot (exp 't (List.Tot.tl c) a) (decreases e) =
  subst1' e 0 payload

let lifts_base' (#a: ('t).ty) (#c: context 't) (e: exp_base 't c a) (n: C.index_insert c) (c': context 't): Tot (exp_base 't (C.lifts c n c') a) =
  match e with
  | XVal v -> XVal v
  | XBVar i ->
    let c'' = C.lifts c n c' in
    let i' = C.index_lifts i n (List.Tot.length c') in
    // TODO PROVE EASY
    assume (C.get_index c'' i' == a);
    XBVar i'
  | XVar x' ->
    XVar x'

let rec lifts' (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (n: C.index_insert c) (c': context 't): Tot (exp 't (C.lifts c n c') a) (decreases e) =
  match e with
  | XBase e1 -> XBase (lifts_base' e1 n c')
  | XApps e1 -> XApps (lifts_apps' e1 n c')
  | XFby v e -> XFby v (lifts' e n c')
  | XMu e1 ->
    XMu (lifts' e1 (n + 1) c')
  | XLet b e1 e2 -> XLet b (lifts' e1 n c') (lifts' e2 (n + 1) c')
  | XContract ps r g i -> XContract ps (lifts' r n c') (lifts' g (n + 1) c') (lifts' i n c')
  | XCheck name e1 -> XCheck name (lifts' e1 n c')
and lifts_apps' (#a: funty ('t).ty) (#c: context 't) (e: exp_apps 't c a) (n: C.index_insert c) (c': context 't): Tot (exp_apps 't (C.lifts c n c') a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f e -> XApp (lifts_apps' f n c') (lifts' e n c')


let lifts (#a: ('t).ty) (#c: context 't) (e: exp 't c a) (c': context 't): Tot (exp 't (C.append c' c) a) =
  lifts' e 0 c'
