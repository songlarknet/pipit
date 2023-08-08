(* Blessed expressions.
    Blessed expressions
*)
module Pipit.Exp.Blessed

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep

let rec exp_is_blessed (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> exp_apps_is_blessed e1
  | XFby _ e1 -> exp_is_blessed e1
  | XMu e1 -> exp_is_blessed e1
  | XLet b e1 e2 -> exp_is_blessed e1 /\ exp_is_blessed e2
  | XCheck _ e1 -> exp_is_blessed e1
  | XContract r g i ->
    bigstep_contract_valid r g i /\
    exp_is_blessed r /\
    exp_is_blessed g

and exp_apps_is_blessed (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 -> exp_apps_is_blessed e1 /\ exp_is_blessed e2

type exp_blessed (t: table) (c: context t) (a: t.ty) = e: exp t c a { exp_is_blessed e }

type exp_apps_blessed (t: table) (c: context t) (a: funty t.ty) = e: exp_apps t c a { exp_apps_is_blessed e }
