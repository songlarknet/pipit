module Pipit.Norm.FromExp

open Pipit.Prim.Table

open Pipit.Norm.Context
open Pipit.Norm.Defs
open Pipit.Norm.Exp

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties
module CR = Pipit.Context.Row

module X  = Pipit.Exp.Base


let rec dstate_of_exp
  (#t: table) (#c: context t)
  (e: X.exp t c 'a)
    : Tot (context t) (decreases e) =
  match e with
  | X.XVal _ | X.XBVar _ | X.XVar _ | X.XPrim _ -> []
  | X.XApp e e' ->
    dstate_of_exp e `C.append` dstate_of_exp e'
  | X.XFby v e' ->
    // TODO need valty for fby buf
    // (X.XFby?.valty e) ::
      dstate_of_exp e'
  | X.XThen e e' ->
    dstate_of_exp e `C.append` dstate_of_exp e'
  | X.XMu e' ->
    dstate_of_exp e'
  | X.XLet b e e' ->
    dstate_of_exp e `C.append` dstate_of_exp e'
  | X.XCheck p e e' ->
    dstate_of_exp e `C.append` dstate_of_exp e'

let split
  (#t: table) (#ci #cd: context t) (#ty: t.ty)
  (n: norm_base t (NC ci (ty :: cd)) ty):
    cd1: context t & cd2: context t &
    d1:  ndefs   t (NC ci cd1)     &
    d2:  ndefs   t (NC (C.rev_acc cd1 ci) (ty :: cd2))
      { cd = cd1 `C.append` cd2 /\
        state_of_ndefs d1 == state_of_ndefs n.sys.defs /\
        Nil? (state_of_ndefs d2)
        /\ (forall (ri: row ci) (st: row (state_of_ndefs n.sys.defs)) (st': row (state_of_ndefs n.sys.defs)) (r1: row cd1) (r2: row cd2) (v: t.ty_sem ty).
        (
          let rd: row cd = coerce_eq () (CR.append r1 r2) in
          let rtd: row (ty :: cd) = (v, rd) in
          let ritd: row (nc_all (NC ci (ty :: (cd1 `C.append` cd2)))) = CR.rev_acc rtd ri in
          let rt2: row (ty :: cd2) = (v, r2) in
          let ri1: row (C.rev_acc cd1 ci) = CR.rev_acc r1 ri in
          let ri1t2: row (nc_all (NC (C.rev_acc cd1 ci) ((ty :: cd2)))) = CR.rev_acc rt2 ri1 in
          ndefs_sem _ _ n.sys.defs ri st ritd st' <==>
            (ndefs_sem _ _ d1 ri st (CR.rev_acc r1 ri) st' /\ ndefs_sem _ _ d2 (CR.rev_acc r1 ri) () ri1t2 ())))
      }
  = admit ()

(*
let rec translate
  (#t: table) (#c: context t) (#ty: t.ty)
  (e: X.val_exp t c ty):
    c': context t & n: norm_base t (NC c c') ty { state_of_ndefs n.sys.defs = dstate_of_exp e } =
  match e with
  | X.XVal v -> { sys = empty; exp = NXVal v }
  | X.XBVar i -> {sys = empty; exp = NXBVar i }
  | X.XVar _ -> false_elim ()
  | X.XPrim _ -> xxx
  | X.XApp _ _ -> xxx
  | X.XFby v e' ->
    let (| c', n' |) = translate e' in
    let nx: nexp_base t (C.rev_acc c (ty :: c')) = lift n'.exp (length c') in
    let d: ndefs t (NC c (ty :: c')) =
      NDCons (NDFby v nx) n'.sys.defs
      in
    xxx
  | X.XThen _ _ -> xxx
  | X.XMu e' ->
    let (| c', n' |) = translate e' in
    let (| cd1, cd2, n1, n2 |) = split n' in
    let n'' = nbinds n1 n2 in
    let nx = NXBVar (List.length cd2) in
    { sys = n''; exp = nx }
  | X.XLet b e1 e2 ->
    let (| c1, n1 |) = translate e1 in
    let (| c2, n2 |) = translate e2 in
    nbinds n1 (nLet n1.exp (nlifts 1 (List.length c1) n2))
  | X.XCheck p e1 e2 ->
    let (| c1, n1 |) = translate e1 in
    let (| c2, n2 |) = translate e2 in
    nbinds n1 (nprop p n1.exp (nlifts 0 (List.length c1) n2))
*)
