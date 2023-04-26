(* TODO update to typed exprs*)
module Pipit.Exp.Subst

open Pipit.Exp.Base

(*
let rec lift_lift_commute (e: exp) (x1: var) (x2: var { x2 <= x1 }):
  Lemma (ensures lift (lift e x1) x2 == lift (lift e x2) (x1 + 1)) =
  match e with
  | XVal _ -> ()
  | XVar _ -> ()
  | XPrim2 _ e1 e2 ->
    lift_lift_commute e1 x1 x2;
    lift_lift_commute e2 x1 x2
  | XIte ep e1 e2 ->
    lift_lift_commute ep x1 x2;
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
  | XIte ep e1 e2 ->
    subst_lift_id ep p x;
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

*)
