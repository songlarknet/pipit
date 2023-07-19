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
type ncontext (t: table) = | NC:
  available: context t ->
  remainder: context t ->
  ncontext t

type ncontext_focus (t: table) = | NCF:
  available: context t ->
  valty:     t.ty ->
  remainder: context t ->
  ncontext_focus t

let ncf_next (#t: table) (ncf: ncontext_focus t): ncontext t =
  NC (ncf.valty :: ncf.available) ncf.remainder

let ncf_prev (#t: table) (ncf: ncontext_focus t): ncontext t =
  NC ncf.available (ncf.valty :: ncf.remainder)

let ncf_available (#t: table) (ncf: ncontext_focus t): context t =
  ncf.available

let ncf_all (#t: table) (ncf: ncontext_focus t): context t =
  List.Tot.rev_acc ncf.remainder (ncf.valty :: ncf.available)
  // == List.Tot.rev_acc (ncf.valty :: ncf.remainder) ncf.available

let nc_all (#t: table) (nc: ncontext t): context t =
  List.Tot.rev_acc nc.remainder nc.available
  // ncf_all ncf == nc_all (ncf_next ncf) == nc_all (ncf_prev ncf)

type ndef (t: table) (ncf: ncontext_focus t): Type =
 | NDLet: e: nexp t (ncf_available ncf) ncf.valty ->
          ndef t ncf
 | NDFby: v: t.ty_sem ncf.valty ->
          e: nexp t (ncf_all ncf) ncf.valty ->
          ndef t ncf
 | NDFree: ndef t ncf


type ndefs (t: table): ncontext t -> Type =
 | NDNil: #cbound: context t -> ndefs t (NC cbound [])
 | NDCons:
      #ncf: ncontext_focus t ->
      def:  ndef  t ncf ->
      rest: ndefs t (ncf_next ncf) ->
      ndefs t (ncf_prev ncf)

type nprop (t: table) (c: context t) = {
  name: string;
  antecedents: list (nexp t c t.propty);
  consequent: nexp t c t.propty;
}

type nsys (t: table) (nc: ncontext t) = {
  defs:   ndefs t nc;
  checks: list (nprop t (nc_all nc));
}

type norm (t: table) (nc: ncontext t) (ty: t.ty) = {
  sys: nsys t nc;
  exp: nexp t (nc_all nc) ty;
}

type norm_apps (t: table) (nc: ncontext t) (ty: funty t.ty) = {
  sys: nsys t nc;
  exp: nexp_apps t (nc_all nc) ty;
}

assume val nsys_is_deterministic (#t: table) (#nc: ncontext t) (n: nsys t nc): bool
// check if any NDFree

assume val nexp_lift (#t: table) (#c: context t) (#ty: t.ty) (n: nexp t c ty) (c': context t): nexp t (c' `List.Tot.rev_acc` c) ty
assume val nexp_sem (#t: table) (#c: context t) (#ty: t.ty) (i: row c) (n: nexp t c ty): t.ty_sem ty

let rec state_of_ndefs (#t: table) (#nc: ncontext t) (n: ndefs t nc): Tot (context t) (decreases n)
 = match n with
 | NDNil -> []
 | NDCons (NDFby _ _) rest ->
    (NDCons?.ncf n).valty :: state_of_ndefs rest
 | NDCons _ rest -> state_of_ndefs rest

noeq
type ndefs_sem (t: table):
  // Program `n`, typed with definition context `nc`
  nc: ncontext t -> n: ndefs t nc ->
  // with given input environment and state
     row nc.available -> row (state_of_ndefs n) ->
  // evaluates to new state, and collected output environment
     row (nc_all nc)  -> row (state_of_ndefs n) -> Type =
  // To evaluate an empty definition context:
  | NDSNil:
      c:       context t ->
      inputs:  row c ->
      // a program with no definitions `NDNil`
      // with environment `inputs` and empty state `()`
      // evaluates to empty state `()` and copies output environment `inputs`.
      ndefs_sem t (NC c []) NDNil
        inputs ()
        inputs ()
  // To evaluate a let or pure expression:
  | NDSLet:
      // for a focussed context `ncf`,
      ncf:     ncontext_focus t ->
      // we have an expression `e` that can refer to the current bindings in `ncf`
      e:       nexp t (ncf_available ncf) ncf.valty ->
      // and the remaining definitions `n'`
      n':      ndefs t (ncf_next ncf) ->
      // with environment `inputs` and initial state `st`
      inputs:  row (ncf_available ncf) ->
      st:      row (state_of_ndefs n') ->
      // output environment `outputs` and result state `st'`
      outputs: row (ncf_all ncf) ->
      st':     row (state_of_ndefs n') ->
      // we evaluate the current expression `nexp_sem inputs e` and add it to the input environment;
      // we then evaluate the remaining definitions `n'` to result state `st'` and environment `outputs`.
      ndefs_sem t (ncf_next ncf) n'
        (nexp_sem inputs e, inputs) st
         outputs                    st' ->
      // So that's how you evaluate a let definition.
      ndefs_sem t (ncf_prev ncf) (NDCons (NDLet e) n')
        inputs  st
        outputs st'
  // To evaluate a follow-by definition:
  | NDSFby:
      // for a focussed context `ncf`,
      ncf:     ncontext_focus t ->
      // the pieces of the follow-by: initial value and expression
      v_init:  t.ty_sem ncf.valty ->
      // the expression can refer to all bindings, including later definitions - unlike pure expressions which can only refer to previously-bound definitions
      e:       nexp t (ncf_all ncf) ncf.valty ->
      // for remaining definitions `n'`
      n':      ndefs t (ncf_next ncf) ->

      // with environment `inputs`
      inputs:  row (ncf_available ncf) ->
      // our starting state includes the current state for the follow-by `v_state`, as well as the state for the remaining definitions `st`
      v_state: t.ty_sem ncf.valty ->
      st:      row (state_of_ndefs n') ->

      // and we get a result environment `outputs` and result state `st'`
      outputs: row (ncf_all ncf) ->
      st':     row (state_of_ndefs n') ->
      // we evaluate the remaining definitions, binding the current value of our follow-by to `v_state`
      ndefs_sem t (ncf_next ncf) n'
        (v_state, inputs) st
         outputs          st' ->
      // and finally, in the updated state, we evaluate the follow-by expression, allowing it to refer to the results of all of the definitions (`outputs`)
      ndefs_sem t (ncf_prev ncf) (NDCons (NDFby v_init e) n')
         inputs  (v_state,            st)
         outputs (nexp_sem outputs e, st')
  // To evaluate a free definition:
  | NDSFree:
      // for a focussed context `ncf`,
      ncf:     ncontext_focus t ->
      // free definitions have no expression or anything, so we just need the remaining definitions `n'`
      n':      ndefs t (ncf_next ncf) ->

      // with environment `inputs` and starting state `st`,
      inputs:  row (ncf_available ncf) ->
      st:      row (state_of_ndefs n') ->

      // we get back a result environment `outputs` and result state `st'`
      outputs: row (ncf_all ncf) ->
      st':     row (state_of_ndefs n') ->

      // and, finally, we need some arbitrary value to give the definition
      v_free: t.ty_sem ncf.valty ->
      // we evaluate the remaining definitions, binding our definition to `v_free` in the `inputs` environment.
      ndefs_sem t (ncf_next ncf) n'
        (v_free, inputs) st
         outputs         st' ->
      ndefs_sem t (ncf_prev ncf) (NDCons NDFree n')
         inputs  st
         outputs st'

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

