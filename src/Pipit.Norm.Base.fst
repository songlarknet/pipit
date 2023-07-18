module Pipit.Norm.Base

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

(* Definitions can be pure lets, fby, or "free" with no definition. Definitions
  are parameterised by two contexts: `cbound` for the bindings that have a
  value right now -- these bindings can be used anywhere, in pure expressions
  and in follow-by expressions. The second context `ceverything` are the
  bindings that will be bound by later expressions. Only follow-by expressions
  can refer to these bindings, as they will have a value by the time the
  follow-by wants to read them; pure expressions cannot refer to future
  bindings as their value is not available at the time to evaluate the pure
  expression.
*)
type ndef (t: table) (cbound crest: context t) (valty: t.ty): Type =
 | NDLet: e: nexp t cbound valty ->
          ndef t cbound crest valty
 | NDFby: v: t.ty_sem valty ->
          e: nexp t (crest `List.Tot.rev_acc` cbound) valty ->
          ndef t cbound crest valty
 | NDFree: ndef t cbound crest valty


type ndefs (t: table) (cbound: context t): context t -> Type =
 | NDNil: ndefs t cbound []
 | NDCons:
      #valty: t.ty -> #crest: context t ->
      def:  ndef  t cbound (valty :: crest) valty ->
      rest: ndefs t (valty :: cbound) crest ->
      ndefs t cbound (valty :: crest)

type nprop (t: table) (c: context t) = {
  name: string;
  antecedents: list (nexp t c t.propty);
  consequent: nexp t c t.propty;
}

type nsys (t: table) (c c': context t) = {
  defs:   ndefs t c c';
  checks: list (nprop t (c' `List.Tot.rev_acc` c));
}

type norm (t: table) (c c': context t) (ty: t.ty) = {
  sys: nsys t c c';
  exp: nexp t (c' `List.Tot.rev_acc` c) ty;
}

type norm_apps (t: table) (c c': context t) (ty: funty t.ty) = {
  sys: nsys t c c';
  exp: nexp_apps t (c' `List.Tot.rev_acc` c) ty;
}

assume val nsys_is_deterministic (#t: table) (#c #c': context t) (n: nsys t c c'): bool
// check if any NDFree

assume val nexp_lift (#t: table) (#c: context t) (#ty: t.ty) (n: nexp t c ty) (c': context t): nexp t (c' `List.Tot.rev_acc` c) ty
assume val nexp_sem (#t: table) (#c: context t) (#ty: t.ty) (i: row c) (n: nexp t c ty): t.ty_sem ty

let rec state_of_ndefs (#t: table) (#c #c': context t) (n: ndefs t c c'): Tot (context t) (decreases n)
 = match n with
 | NDNil -> []
 | NDCons (NDFby _ _) rest ->
    NDCons?.valty n :: state_of_ndefs rest
 | NDCons _ rest -> state_of_ndefs rest

noeq
type ndefs_sem (t: table) (c: context t) (inputs: row c):
  c': context t ->
  n: ndefs t c c' ->
  row (state_of_ndefs n) ->
  row (state_of_ndefs n) ->
  row (c' `List.Tot.rev_acc` c) -> Type =
  | NDSNil: ndefs_sem t c inputs [] NDNil () () inputs
  | NDSLet:
      ty: t.ty ->
      e: nexp t c ty ->
      c': context t ->
      n': ndefs t (ty :: c) c' ->
      st: row (state_of_ndefs n') ->
      st': row (state_of_ndefs n') ->
      r': row (List.Tot.rev_acc c' (ty :: c)) ->
      ndefs_sem t (ty :: c) (nexp_sem inputs e, inputs) c' n' st st' r' ->
      ndefs_sem t c inputs (ty :: c') (NDCons (NDLet e) n') st st' r'
  | NDSFby:
      ty: t.ty ->
      v_init:   t.ty_sem ty ->
      v_state:  t.ty_sem ty ->
      c': context t ->
      e: nexp t ((ty :: c') `List.Tot.rev_acc` c) ty ->
      n': ndefs t (ty :: c) c' ->
      st: row (state_of_ndefs n') ->
      st': row (state_of_ndefs n') ->
      r': row (List.Tot.rev_acc c' (ty :: c)) ->
      ndefs_sem t (ty :: c) (v_state, inputs) c' n' st st' r' ->
      ndefs_sem t c inputs (ty :: c') (NDCons (NDFby v_init e) n') (v_state, st) (nexp_sem r' e, st') r'
  | NDSFree:
      ty: t.ty ->
      v_free:   t.ty_sem ty ->
      c': context t ->
      n': ndefs t (ty :: c) c' ->
      st: row (state_of_ndefs n') ->
      st': row (state_of_ndefs n') ->
      r': row (List.Tot.rev_acc c' (ty :: c)) ->
      ndefs_sem t (ty :: c) (v_free, inputs) c' n' st st' r' ->
      ndefs_sem t c inputs (ty :: c') (NDCons NDFree n') st st' r'

// TODO try zipper for c' / c movement. make contexts implicit? write on paper

// let rec norm_get_defs' (#t: table) (#c #c': context t) (n: norm_defs t c c'):
//   Tot (cdefs: context t { c' = cdefs `C.append` c }) (decreases n) =
//   match n with
//   | NDNil -> []
//   | NDCons _ rest ->
//     let ty = NDCons?.valty n in
//     let cdefs = norm_get_defs' rest in
//     // ASSUME snoc/append easy list stuff
//     assume ((cdefs `C.append` (ty :: c)) == (List.Tot.snoc (cdefs, ty)) `C.append` c);
//     List.Tot.snoc (cdefs, ty)

// let norm_get_defs (#t: table) (#c: context t) (#r: context t -> eqtype) (n: norm t c r):
//   (cdefs: context t { n.c' = cdefs `C.append` c }) =
//   norm_get_defs' n.defs


// let union (#t: table) (#c: context t) (n: norm t c) (n': norm t c):
//   norm t c // { sem u = n <+> n' }
//   =
//     let nc = norm_get_defs n in
//     let nc' = norm_get_defs n' in
//     let lift_by = List.Tot.length nc in
//     let ndefs' = lift_defs lift_by n'.defs in
//    {
//     c' =  nc' `C.append` nc `C.append` c;
//     defs = union_defs ndefs' ndefs;
//   }

