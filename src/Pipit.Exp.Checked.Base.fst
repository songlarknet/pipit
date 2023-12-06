(* Checked expressions: expressions that are known to satisfy properties
*)
module Pipit.Exp.Checked.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding
open Pipit.Exp.Causality

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties

module PM = Pipit.Prop.Metadata

// Which is better: inductive relation or recursive definition?
// noeq
// type check (mode: check_mode) (#t: table) (#c: context t): (#a: t.ty) -> list (row c) -> exp t c a -> Type =
//  | CkBase:
//           #valty: t.ty ->
//           streams: list (row c)    ->
//           e: exp_base t c valty    ->
//           check mode streams (XBase e)
//  | CkApps:
//           #valty: t.ty ->
//           streams: list (row c)    ->
//           e: exp_apps t c (FTVal valty)    ->
//           check_apps mode streams e ->
//           check mode streams (XApps e)
//  | CkFby1: #a: t.ty                ->
//            start: list (row c) { List.Tot.length start <= 1 }
//                                    ->
//            v0: t.ty_sem a          ->
//            e: exp t c a            ->
//            check mode start (XFby v0 e)
//  | CkFbyS: #a: t.ty                 ->
//            latest: row c            ->
//            prefix: list (row c) { List.Tot.length prefix >= 1 }
//                                     ->
//            v0: t.ty_sem a           ->
//            e: exp t c a             ->
//            check mode            prefix           e ->
//            check mode (latest :: prefix) (XFby v0 e)

//  | CkMu: #valty: t.ty                         ->
//          streams: list (row c)                ->
//          e: exp t (C.close1 c valty) valty    ->
//          check mode streams (subst1 e (XMu e))     ->
//          check mode streams (XMu e)
//  | CkLet:
//           #a: t.ty -> #b: t.ty                ->
//           streams: list (row c)               ->
//           e1: exp t c b                       ->
//           e2: exp t (C.close1 c b) a          ->
//           check mode streams (subst1 e2 e1)        ->
//           check mode streams (XLet b e1 e2)

//  | CkContract:
//           #valty: t.ty                        ->
//           streams: list (row c)               ->
//           status: contract_status             ->
//           rely: exp t c            t.propty   ->
//           guar: exp t (valty :: c) t.propty   ->
//           impl: exp t c            valty      ->
//           check mode streams rely                  ->
//           check mode streams (subst1 guar impl)    ->
//           check mode streams impl                  ->
//           (Some status.contract_env = mode.check_contract_env ==> bigstep_always streams rely) ->
//           (Some status.contract_impl = mode.check_contract_impl ==> bigstep_contract_valid streams rely guar impl) ->
//           check mode streams (XContract status rely guar impl)

//  | CkCheck:
//           streams: list (row c)                   ->
//           status:  prop_status                    ->
//           eprop:   exp t c             t.propty   ->
//           check mode streams                eprop      ->
//           (Some status = mode.check_assert ==> bigstep_always streams eprop) ->
//           check mode streams (XCheck status eprop)

// and check_apps (mode: check_mode) (#t: table) (#c: context t): (#a: funty t.ty) -> list (row c) -> exp_apps t c a -> Type =
//  (* Primitives `p` are looked up in the primitive table semantics *)
//  | CkPrim:
//           streams: list (row c) ->
//           p: t.prim             ->
//           check_apps mode streams (XPrim p)

//  (* Element-wise application *)
//  | CkApp: streams: list (row c)       ->
//           #a: t.ty -> #b: funty t.ty  ->
//           f: exp_apps t c (FTFun a b) ->
//           e: exp t c  a               ->
//           check_apps mode streams f        ->
//           check      mode streams e        ->
//           check_apps mode streams (XApp f e)



let rec check (#t: table u#i u#j) (#c: context t) (#a: t.ty) (#streams: list (row c)) (#e: exp t c a) (#v: t.ty_sem a)  (mode: PM.check_mode)
(hBS: bigstep streams e v): Tot prop (decreases hBS) =
  match hBS with
  | BSBase _ _ _ _ ->
    True
  | BSApps _ _ _ hBSA' ->
    check_apps mode hBSA'
  | BSFby1 _ _ _ ->
    True
  | BSFbyS _ _ _ _ _ hBS' ->
    check mode hBS'
  | BSMu _ _ _ hBS' ->
    check mode hBS'
  | BSLet _ _ _ _ hBS' ->
    check mode hBS'
  | BSContract _ status rely guar impl _ _ _ hBSr' hBSg' hBSi' ->
    check mode hBSr' /\
    check mode hBSg' /\
    check mode hBSi' /\
    (PM.prop_status_contains mode status ==>
      bigstep_always streams rely) /\
    (bigstep_always streams rely ==>
      bigstep_always streams (subst1 guar impl))
  | BSCheck _ status eprop _ hBS' ->
    check mode hBS' /\
    (PM.prop_status_contains mode status ==>
      bigstep_always streams eprop)

and check_apps (#t: table u#i u#j) (#c: context t) (#a: funty t.ty) (#streams: list (row c)) (#e: exp_apps t c a) (#v: funty_sem t.ty_sem a) (mode: PM.check_mode) (hBSA: bigstep_apps streams e v): Tot prop (decreases hBSA) =
  match hBSA with
  | BSPrim _ _ -> True
  | BSApp _ _ _ _ _ hBSA' hBS' -> check_apps mode hBSA' /\ check mode hBS'

let check' (#t: table u#i u#j) (#c: context t) (#a: t.ty) (mode: PM.check_mode) (e: exp t c a) =
  forall (streams: list (row c)) (v: t.ty_sem a) (hBS: bigstep streams e v).
    check mode hBS

let check_apps' (#t: table) (#c: context t) (#a: funty t.ty) (mode: PM.check_mode) (e: exp_apps t c a) =
  forall (streams: list (row c)) (v: funty_sem t.ty_sem a) (hBS: bigstep_apps streams e v).
    check_apps mode hBS

let check_contract_definition (#t: table) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (rely: exp t c t.propty) (guar: exp t (a::c) t.propty) (impl: exp t c a) =
  forall (streams: list (row c))
    (vr: bool)       (hBSr: bigstep streams rely vr)
    (vg: bool)       (hBSg: bigstep streams (subst1 guar impl) vg)
    (vi: t.ty_sem a) (hBSi: bigstep streams impl vi).
    check mode hBSr /\
    check mode hBSg /\
    check mode hBSi /\
    (bigstep_always streams rely ==>
      bigstep_always streams (subst1 guar impl))

let bigstep_equivalent (#t: table) (#c: context t) (#a: t.ty) (e e': exp t c a): prop =
  forall (streams: list (row c)) (v: t.ty_sem a).
    bigstep streams e v <==> bigstep streams e' v

let check_equivalent (#t: table) (#c: context t) (#a: t.ty) (m m': PM.check_mode) (e e': exp t c a): prop =
  forall (streams: list (row c)) (v: t.ty_sem a) (hBS: bigstep streams e v) (hBS': bigstep streams e' v).
    check m hBS <==> check m' hBS'

let bless_equivalent (#t: table) (#c: context t) (#a: t.ty) (e e': exp t c a): prop =
  bigstep_equivalent e e' /\
  check_equivalent PM.check_mode_all  PM.check_mode_valid   e e' /\
  check_equivalent PM.check_mode_none PM.check_mode_unknown e e'

let rec bless (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot (exp t c a) (decreases e) =
  match e with
  | XBase _ -> e
  | XApps e1 -> XApps (bless_apps e1)
  | XFby v e1 -> XFby v (bless e1)
  | XMu e1 -> XMu (bless e1)
  | XLet b e1 e2 -> XLet b (bless e1) (bless e2)
  | XCheck s e1 -> XCheck PM.PSValid (bless e1)
  | XContract s r g i ->
    XContract PM.PSValid
      (bless r)
      (bless g)
      (bless i)

and bless_apps (#t: table) (#c: context t) (#a: funty t.ty) (e: exp_apps t c a): Tot (exp_apps t c a) (decreases e) =
  match e with
  | XPrim p -> XPrim p
  | XApp f e -> XApp (bless_apps f) (bless e)

let lemma_check_bless (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a { check' PM.check_mode_all e }):
  Lemma (ensures check' PM.check_mode_valid (bless e))
    [SMTPat (check' PM.check_mode_valid (bless e))] =
  // TODO:ADMIT lemma
  admit ()

