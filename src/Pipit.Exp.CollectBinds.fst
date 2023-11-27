(* Working with sets of bindings *)
module Pipit.Exp.CollectBinds

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Checked.Base
open Pipit.Exp.Checked.Compound

module C  = Pipit.Context.Base
module PM = Pipit.Prop.Metadata

module List = FStar.List.Tot

noeq
type bind (t: table) = {
  bind_ty:   t.ty;
  bind_var:  C.var bind_ty;
  bind_expr: cexp t [] bind_ty;
}

let ty_eq (#t: table) (t1 t2: t.ty): b: bool { b ==> t1 == t2 } =
  // Perhaps exposing var_eq instead of ty_eq was not such a good idea
  t.var_eq (C.Var #t.ty #t1 0) (C.Var #t.ty #t2 0)

let expr_base_eq (#t: table) (#ctx: context t) (#ty: t.ty) (e1 e2: exp_base t ctx ty): b: bool { b ==> e1 == e2} =
  match e1 with
  | XVal i ->
    (match e2 with
    | XVal j -> i = j
    | _ -> false)
  | XBVar i ->
    (match e2 with
    | XBVar j -> i = j
    | _ -> false)
  | XVar i ->
    (match e2 with
    | XVar j ->
      t.var_eq i j
    | _ -> false)

let rec expr_eq (#t: table) (#ctx: context t) (#ty: t.ty) (e1 e2: exp t ctx ty)
  : Tot (b: bool { b ==> e1 == e2 })
    (decreases e1) =
  match e1 with
  | XBase i ->
    (match e2 with
    | XBase j -> expr_base_eq i j
    | _ -> false)
  | XApps i ->
    (match e2 with
    | XApps j -> expr_apps_eq i j
    | _ -> false)
  | XFby i i' ->
    (match e2 with
    | XFby j j' -> i = j && expr_eq i' j'
    | _ -> false)
  | XMu i ->
    (match e2 with
    | XMu j -> expr_eq i j
    | _ -> false)
  | XLet it i i' ->
    (match e2 with
    | XLet jt j j' -> ty_eq it jt && expr_eq i j && expr_eq i' j'
    | _ -> false)
  | XContract is ir ig ii ->
    (match e2 with
    | XContract js jr jg ji ->
      is = js && expr_eq ir jr && expr_eq ig jg && expr_eq ii ji
    | _ -> false)
  | XCheck is i ->
    (match e2 with
    | XCheck js j -> is = js && expr_eq i j
    | _ -> false)

and
 expr_apps_eq (#t: table) (#ctx: context t) (#ty: funty t.ty) (e1 e2: exp_apps t ctx ty)
  : Tot (b: bool { b ==> e1 == e2 })
    (decreases e1) =
 match e1 with
 | XPrim i ->
  (match e2 with
  | XPrim j -> t.prim_eq i j
  | _ -> false)
 | XApp i i' ->
  (match e2 with
  | XApp j j' ->
    let t1 = XApp?.arg e1 in
    let t2 = XApp?.arg e2 in
    ty_eq t1 t2 && expr_apps_eq i j && expr_eq i' j'
  | _ -> false)


let rec exp_free_contains (#t: table) (#ctx: context t) (#ty: t.ty) (e: exp t ctx ty) (keep: list nat)
  : Tot bool
    (decreases e) =
  match e with
  | XBase (XVar i) ->
    List.mem (C.Var?.v i) keep
  | XBase _ -> false
  | XApps i ->
    exp_apps_free_contains i keep
  | XFby i i' ->
    exp_free_contains i' keep
  | XMu i ->
    exp_free_contains i keep
  | XLet it i i' ->
    exp_free_contains i keep || exp_free_contains i' keep
  | XContract is ir ig ii ->
    exp_free_contains ir keep || exp_free_contains ig keep || exp_free_contains ii keep
  | XCheck is i ->
    exp_free_contains i keep

and
 exp_apps_free_contains (#t: table) (#ctx: context t) (#ty: funty t.ty) (e: exp_apps t ctx ty) (keep: list nat)
  : Tot bool
    (decreases e) =
 match e with
 | XPrim i -> false
 | XApp i i' -> exp_apps_free_contains i keep || exp_free_contains i' keep

let rec find_equivalent (#t: table) (#ty: t.ty) (binds: list (bind t)) (def: cexp t [] ty): option (C.var ty) =
  match binds with
  | [] -> None
  | b::binds ->
    if ty_eq b.bind_ty ty &&
       expr_eq b.bind_expr def
    then Some b.bind_var
    else find_equivalent binds def

let rec binds_to_lets (#t: table) (#ty: t.ty) (binds: list (bind t)) (body: cexp t [] ty): cexp t [] ty =
  match binds with
  | [] -> body
  | b::binds ->
    let body = close1 body b.bind_var in
    let body = XLet b.bind_ty b.bind_expr body in
    binds_to_lets binds body

let rec dependent_binds (#t: table) (binds: list (bind t)) (keep: list nat): (list (bind t) & list (bind t)) =
  match binds with
  | [] -> ([], [])
  | b :: binds ->
    if exp_free_contains b.bind_expr keep
    then
      let (here, later) = dependent_binds binds (C.Var?.v b.bind_var :: keep) in
      (b :: here, later)
    else
      let (here, later) = dependent_binds binds keep in
      (here, b :: later)
