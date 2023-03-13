module Pipit.Exp.Subst

open Pipit.Exp.Base

(* Lifting de Bruijn indices, bookkeeping used by substitution *)
let rec lift (e: exp) (above: var) : exp =
  match e with
  | XVal v -> XVal v
  | XVar x ->
    if x >= above
    then XVar (x + 1)
    else XVar x
  | XPrim2 p e1 e2 ->
    XPrim2 p (lift e1 above) (lift e2 above)
  | XPre e ->
    XPre (lift e above)
  | XThen e1 e2 ->
    XThen (lift e1 above) (lift e2 above)
  | XMu e ->
    XMu (lift e (above + 1))
  | XLet e1 e2 ->
    XLet (lift e1 above) (lift e2 (above + 1))

(* Substitution *)
let rec subst (e: exp) (x: var) (payload: exp) : exp =
  match e with
  | XVal v -> XVal v
  | XVar x' ->
    if x' = x
    then payload
    else if x' > x
    then XVar (x' - 1)
    else XVar x'
  | XPrim2 p e1 e2 ->
    XPrim2 p (subst e1 x payload) (subst e2 x payload)
  | XPre e ->
    XPre (subst e x payload)
  | XThen e1 e2 ->
    XThen (subst e1 x payload) (subst e2 x payload)
  | XMu e ->
    XMu (subst e (x + 1) (lift payload 0))
  | XLet e1 e2 ->
    XLet (subst e1 x payload) (subst e2 (x + 1) (lift payload 0))

(* Properties *)
let rec lift_preserves_wf (e: exp) (n x: var):
  Lemma (requires wf e n)
        (ensures wf (lift e x) (n + 1)) =
 match e with
 | XVal _ -> ()
 | XVar x' -> ()
 | XPrim2 _ e1 e2 ->
   lift_preserves_wf e1 n x;
   lift_preserves_wf e2 n x
 | XPre e1 -> lift_preserves_wf e1 n x
 | XThen e1 e2 ->
   lift_preserves_wf e1 n x;
   lift_preserves_wf e2 n x
 | XMu e1 -> lift_preserves_wf e1 (n + 1) (x + 1)
 | XLet e1 e2 ->
   lift_preserves_wf e1 n x;
   lift_preserves_wf e2 (n + 1) (x + 1)

let rec subst_preserves_wf (e p: exp) (n: var) (x: var { x < n + 1 }):
  Lemma (requires wf e (n + 1) /\ wf p n)
        (ensures wf (subst e x p) n) =
  match e with
  | XVal _ -> ()
  | XVar x' -> ()
  | XPrim2 _ e1 e2 ->
    subst_preserves_wf e1 p n x;
    subst_preserves_wf e2 p n x
  | XPre e1 -> subst_preserves_wf e1 p n x
  | XThen e1 e2 ->
    subst_preserves_wf e1 p n x;
    subst_preserves_wf e2 p n x
  | XMu e1 ->
    lift_preserves_wf p n 0;
    subst_preserves_wf e1 (lift p 0) (n + 1) (x + 1)
  | XLet e1 e2 ->
    lift_preserves_wf p n 0;
    subst_preserves_wf e1 p n x;
    subst_preserves_wf e2 (lift p 0) (n + 1) (x + 1)

let rec lift_lift_commute (e: exp) (x1: var) (x2: var { x2 <= x1 }):
  Lemma (ensures lift (lift e x1) x2 == lift (lift e x2) (x1 + 1)) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 _ e1 e2 ->
    lift_lift_commute e1 x1 x2;
    lift_lift_commute e2 x1 x2
  | XPre e1 -> lift_lift_commute e1 x1 x2
  | XThen e1 e2 ->
    lift_lift_commute e1 x1 x2;
    lift_lift_commute e2 x1 x2
  | XMu e1 ->
    lift_lift_commute e1 (x1 + 1) (x2 + 1)
  | XLet e1 e2 ->
    lift_lift_commute e1 x1 x2;
    lift_lift_commute e2 (x1 + 1) (x2 + 1)

let rec subst_lift_id (e p: exp) (x: var):
  Lemma (ensures subst (lift e x) x p == e) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 _ e1 e2 ->
    subst_lift_id e1 p x;
    subst_lift_id e2 p x
  | XPre e1 -> subst_lift_id e1 p x
  | XThen e1 e2 ->
    subst_lift_id e1 p x;
    subst_lift_id e2 p x
  | XMu e1 ->
    subst_lift_id e1 (lift p 0) (x + 1)
  | XLet e1 e2 ->
    subst_lift_id e1 p x;
    subst_lift_id e2 (lift p 0) (x + 1)

let rec lift_subst_distribute_le (e p: exp) (x1: var) (x2: var { x2 <= x1 }):
  Lemma (ensures lift (subst e x1 p) x2 == subst (lift e x2) (x1 + 1) (lift p x2)) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 _ e1 e2 ->
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 p x1 x2
  | XPre e1 -> lift_subst_distribute_le e1 p x1 x2
  | XThen e1 e2 ->
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 p x1 x2
  | XMu e1 ->
    lift_subst_distribute_le e1 (lift p 0) (x1 + 1) (x2 + 1);
    lift_lift_commute p x2 0
  | XLet e1 e2 ->
    lift_subst_distribute_le e1 p x1 x2;
    lift_subst_distribute_le e2 (lift p 0) (x1 + 1) (x2 + 1);
    lift_lift_commute p x2 0

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
  | XPre e1 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2
  | XThen e1 e2 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2;
    subst_subst_distribute_le e2 p1 p2 x1 x2
  | XMu e1 ->
    subst_subst_distribute_le e1 (lift p1 0) (lift p2 0) (x1 + 1) (x2 + 1);
    lift_lift_commute p2 x1 0;
    lift_subst_distribute_le p1 p2 x2 0
  | XLet e1 e2 ->
    subst_subst_distribute_le e1 p1 p2 x1 x2;
    subst_subst_distribute_le e2 (lift p1 0) (lift p2 0) (x1 + 1) (x2 + 1);
    lift_lift_commute p2 x1 0;
    lift_subst_distribute_le p1 p2 x2 0

let subst_subst_distribute_XMu (e p: exp) (x: var):
  Lemma (ensures subst (subst e 0 (XMu e)) x p ==
                 subst (subst e (x + 1) (lift p 0)) 0 (XMu (subst e (x + 1) (lift p 0)))) =
 subst_subst_distribute_le e (XMu e) p 0 x
