(* Checked expressions: expressions that are known to satisfy properties
*)
module Pipit.Exp.Checked.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding

module C  = Pipit.Context.Base
module PM = Pipit.Prop.Metadata

[@@no_auto_projectors]
noeq
type check (mode: PM.check_mode) (#t: table u#i u#j) (#c: context t): (#a: t.ty) -> list (row c) -> exp t c a -> Type =
 | CkBase:
          #valty: t.ty ->
          streams: list (row c)    ->
          e: exp_base t c valty    ->
          check mode streams (XBase e)
 | CkApps:
          #valty: t.ty ->
          streams: list (row c)    ->
          e: exp_apps t c (FTVal valty)    ->
          check_apps mode streams e ->
          check mode streams (XApps e)
 | CkFby1: #a: t.ty                ->
           start: list (row c) { List.Tot.length start <= 1 }
                                   ->
           v0: t.ty_sem a          ->
           e: exp t c a            ->
           check mode start (XFby v0 e)
 | CkFbyS: #a: t.ty                 ->
           latest: row c            ->
           prefix: list (row c) { List.Tot.length prefix >= 1 }
                                    ->
           v0: t.ty_sem a           ->
           e: exp t c a             ->
           check mode            prefix           e ->
           check mode (latest :: prefix) (XFby v0 e)

 | CkMu: #valty: t.ty                         ->
         streams: list (row c)                ->
         e: exp t (C.close1 c valty) valty    ->
         check mode streams (subst1 e (XMu e))     ->
         check mode streams (XMu e)
 | CkLet:
          #a: t.ty -> #b: t.ty                ->
          streams: list (row c)               ->
          e1: exp t c b                       ->
          e2: exp t (C.close1 c b) a          ->
          check mode streams (subst1 e2 e1)        ->
          check mode streams (XLet b e1 e2)

 | CkContract:
          #valty: t.ty                        ->
          streams: list (row c)               ->
          status: PM.contract_status             ->
          rely: exp t c            t.propty   ->
          guar: exp t (valty :: c) t.propty   ->
          impl: exp t c            valty      ->
          squash (PM.prop_status_contains mode status ==> bigstep_always streams rely) ->
          squash (PM.prop_status_contains mode PM.PSValid ==>
            bigstep_always streams rely ==>
            bigstep_always streams (subst1 guar impl)) ->
          check mode streams rely                  ->

          // if rely is true, then impl & guar check ok.
          // this is stated as a semi-classical implication because we need the
          // checks to be strictly smaller than the resulting check.
          // a function impliciation here (`bigstep_always -> check & check`)
          // makes induction difficult.
          // note that bigstep_always is decidable.
          either (~ (bigstep_always streams rely))
            (check mode streams impl &
            check mode streams (subst1 guar impl)) ->

          check mode streams (XContract status rely guar impl)

 | CkCheck:
          streams: list (row c)                   ->
          status:  PM.prop_status                    ->
          eprop:   exp t c             t.propty   ->
          check mode streams                eprop      ->
          squash (PM.prop_status_contains mode status ==>
            bigstep_always streams eprop) ->
          check mode streams (XCheck status eprop)

and check_apps (mode: PM.check_mode) (#t: table) (#c: context t): (#a: funty t.ty) -> list (row c) -> exp_apps t c a -> Type =
 (* Primitives `p` are looked up in the primitive table semantics *)
 | CkPrim:
          streams: list (row c) ->
          p: t.prim             ->
          check_apps mode streams (XPrim p)

 (* Element-wise application *)
 | CkApp: streams: list (row c)       ->
          #a: t.ty -> #b: funty t.ty  ->
          f: exp_apps t c (FTFun a b) ->
          e: exp t c  a               ->
          check_apps mode streams f        ->
          check      mode streams e        ->
          check_apps mode streams (XApp f e)


let check_all (#t: table u#i u#j) (#c: context t) (#a: t.ty) (mode: PM.check_mode) (e: exp t c a) =
  forall (streams: list (row c)).
    squash (check mode streams e)

let check_all_apps (#t: table u#i u#j) (#c: context t) (#a: funty t.ty) (mode: PM.check_mode) (e: exp_apps t c a) =
  forall (streams: list (row c)).
    squash (check_apps mode streams e)

let contract_valid (#t: table) (#c: context t) (#a: t.ty)
  (rely: exp t c t.propty) (guar: exp t (a::c) t.propty) (impl: exp t c a) =
  forall (streams: list (row c)).
  check PM.check_mode_unknown streams rely ==>
  check PM.check_mode_unknown streams impl ==>
  check PM.check_mode_unknown streams (subst1 guar impl) ==>
  bigstep_always streams rely ==>
    (check PM.check_mode_unknown streams rely /\
    check PM.check_mode_unknown streams impl /\
    check PM.check_mode_unknown streams (subst1 guar impl) /\
    bigstep_always streams (subst1 guar impl))

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
