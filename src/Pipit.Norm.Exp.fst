module Pipit.Norm.Exp

open Pipit.Prim.Table

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties
module CR = Pipit.Context.Row

type nexp_base (t: table) (c: context t): t.ty -> Type =
  | NXVal   : #valty: t.ty -> v: t.ty_sem valty -> nexp_base t c valty
  // bound variable (de Bruijn index)
  | NXBVar  : i: C.index_lookup c -> nexp_base t c (C.get_index c i)
  // no free variables: free variables are only necessary for the front-end sugar. we probably don't need sugar for normalised expressions
  // | NXVar   : #valty: t.ty -> x: C.var valty -> nexp_base t c valty

type nexp_apps (t: table) (c: context t): funty t.ty -> Type =
  | NXAPrim: p: t.prim ->
             nexp_apps t c (t.prim_ty p)
  | NXACons : #arg: t.ty -> #res: funty t.ty ->
              nexp_apps t c (FTFun arg res) ->
              nexp_base t c arg ->
              nexp_apps t c res

type nexp (t: table) (c: context t) (ty: t.ty) =
 | NXBase: nexp_base t c ty ->
           nexp t c ty
 | NXApps: nexp_apps t c (FTVal ty) ->
           nexp t c ty


let nexp_base_sem (#t: table) (#c: context t) (#ty: t.ty) (r: row c) (n: nexp_base t c ty): t.ty_sem ty =
  match n with
  | NXVal v -> v
  | NXBVar i -> CR.index _ r i

let rec nexp_apps_sem (#t: table) (#c: context t) (#ty: funty t.ty) (r: row c) (n: nexp_apps t c ty):
  Tot (funty_sem t.ty_sem ty) (decreases n) =
  match n with
  | NXAPrim p -> t.prim_sem p
  | NXACons f a -> (nexp_apps_sem r f) (nexp_base_sem r a)

let nexp_sem (#t: table) (#c: context t) (#ty: t.ty) (r: row c) (n: nexp t c ty): t.ty_sem ty =
  match n with
  | NXBase b -> nexp_base_sem r b
  | NXApps a -> nexp_apps_sem r a



let nexp_base_lift (#t: table) (#c: context t) (#ty: t.ty) (n: nexp_base t c ty) (c': context t):
  n': nexp_base t (c' `C.rev_acc` c) ty
    { forall (r: row c) (r': row c'). nexp_base_sem r n == nexp_base_sem (r' `CR.rev_acc` r) n' }
  =
  match n with
  | NXVal v -> NXVal v
  | NXBVar i ->
    lemma_rev_acc_index_lift c' c i;
    // TODO row indexing lemma why need ===?
    assume (forall (r: row c) (r': row c'). CR.index (context_sem c) r i === (CR.index (context_sem (c' `C.rev_acc` c)) (r' `CR.rev_acc` r) (i + List.Tot.length c')));
    NXBVar (i + List.Tot.length c')

let rec nexp_apps_lift (#t: table) (#c: context t) (#ty: funty t.ty) (n: nexp_apps t c ty) (c': context t):
  Tot
    (n': nexp_apps t (c' `C.rev_acc` c) ty
      { forall (r: row c) (r': row c'). nexp_apps_sem r n == nexp_apps_sem (r' `CR.rev_acc` r) n' })
    (decreases n) =
  match n with
  | NXAPrim p -> NXAPrim p
  | NXACons f a -> NXACons (nexp_apps_lift f c') (nexp_base_lift a c')

let nexp_lift (#t: table) (#c: context t) (#ty: t.ty) (n: nexp t c ty) (c': context t):
  n': nexp t (c' `C.rev_acc` c) ty
    { forall (r: row c) (r': row c'). nexp_sem r n == nexp_sem (r' `CR.rev_acc` r) n' }
   =
  match n with
  | NXBase b -> NXBase (nexp_base_lift b c')
  | NXApps a -> NXApps (nexp_apps_lift a c')


// let nexp_base_weaken (#t: table) (#c: context t) (#ty: t.ty) (n: nexp_base t c ty) (c': context t): nexp_base t (c `C.rev_acc` c') ty =
//   match n with
//   | NXVal v -> NXVal v
//   | NXBVar i ->
//     lemma_rev_acc_index_weaken t c c' i;
//     NXBVar #t #(C.rev_acc c c') i
