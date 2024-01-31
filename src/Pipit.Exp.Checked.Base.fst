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

open FStar.Squash

[@@no_auto_projectors]
noeq
type check (mode: PM.check_mode) (#t: table) (#c: context t): (#a: t.ty) -> list (row c) -> exp t c a -> Type =
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
          (PM.prop_status_contains mode status -> bigstep_always streams rely) ->
          (PM.prop_status_contains mode PM.PSValid ->
            bigstep_always streams rely ->
            bigstep_always streams (subst1 guar impl)) ->
          check mode streams rely                  ->

          // if rely is true, then impl & guar check ok.
          // this is stated as a semi-classical implication because we need the
          // checks to be strictly smaller than the resulting check.
          // a function impliciation here (`bigstep_always -> check & check`)
          // makes induction difficult.
          // note that bigstep_always is decidable.
          either (bigstep_always streams rely -> False)
            (check mode streams impl &
            check mode streams (subst1 guar impl)) ->

          check mode streams (XContract status rely guar impl)

 | CkCheck:
          streams: list (row c)                   ->
          status:  PM.prop_status                    ->
          eprop:   exp t c             t.propty   ->
          check mode streams                eprop      ->
          (PM.prop_status_contains mode status ->
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


let check_all (#t: table) (#c: context t) (#a: t.ty) (mode: PM.check_mode) (e: exp t c a) =
  forall (streams: list (row c)).
    check mode streams e

let check_apps_all (#t: table) (#c: context t) (#a: funty t.ty) (mode: PM.check_mode) (e: exp_apps t c a) =
  forall (streams: list (row c)).
    check_apps mode streams e

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


let rec lemma_bless_distributes_lift (#t: table) (#c: context t) (#t1: t.ty)
  (e1: exp t c t1)
  (ix: C.index_insert c)
  (t2: t.ty):
    Lemma
      (ensures bless (lift1' e1 ix t2) == lift1' (bless e1) ix t2)
      (decreases e1) =
  match e1 with
  | XBase _ -> ()
  | XApps ea -> lemma_bless_distributes_lift_apps ea ix t2
  | XFby v e1' -> lemma_bless_distributes_lift e1' ix t2
  | XMu e1' ->
    lemma_bless_distributes_lift e1' (ix + 1) t2
  | XLet b e1' e2' ->
    lemma_bless_distributes_lift e1'  ix      t2;
    lemma_bless_distributes_lift e2' (ix + 1) t2
  | XCheck s e1' ->
    lemma_bless_distributes_lift e1' ix t2
  | XContract s r g i ->
    lemma_bless_distributes_lift r  ix      t2;
    lemma_bless_distributes_lift g (ix + 1) t2;
    lemma_bless_distributes_lift i  ix      t2

and lemma_bless_distributes_lift_apps (#t: table) (#c: context t) (#t1: funty t.ty)
  (e1: exp_apps t c t1)
  (ix: C.index_insert c)
  (t2: t.ty):
    Lemma
      (ensures bless_apps (lift1_apps' e1 ix t2) == lift1_apps' (bless_apps e1) ix t2)
      (decreases e1) =
  match e1 with
  | XPrim p -> ()
  | XApp f e ->
    lemma_bless_distributes_lift_apps f ix t2;
    lemma_bless_distributes_lift e ix t2




let rec lemma_bless_distributes_subst (#t: table) (#c: context t) (#t1: t.ty)
  (e1: exp t c t1)
  (ix: C.index_lookup c)
  (e2: exp t (C.drop1 c ix) (C.get_index c ix)):
    Lemma
      (ensures bless (subst1' e1 ix e2) == subst1' (bless e1) ix (bless e2))
      (decreases e1) =
  match e1 with
  | XBase _ -> ()
  | XApps ea -> lemma_bless_distributes_subst_apps ea ix e2
  | XFby v e1' -> lemma_bless_distributes_subst e1' ix e2
  | XMu e1' ->
    lemma_bless_distributes_lift  e2 0 t1;
    lemma_bless_distributes_subst e1' (ix + 1) (lift1 e2 t1)
  | XLet b e1' e2' ->
    lemma_bless_distributes_lift  e2 0 b;
    lemma_bless_distributes_subst e1'  ix      e2;
    lemma_bless_distributes_subst e2' (ix + 1) (lift1 e2 b)
  | XCheck s e1' ->
    lemma_bless_distributes_subst e1' ix e2
  | XContract s r g i ->
    lemma_bless_distributes_lift  e2 0 t1;
    lemma_bless_distributes_subst r  ix      e2;
    lemma_bless_distributes_subst g (ix + 1) (lift1 e2 t1);
    lemma_bless_distributes_subst i  ix      e2

and lemma_bless_distributes_subst_apps (#t: table) (#c: context t) (#t1: funty t.ty)
  (e1: exp_apps t c t1)
  (ix: C.index_lookup c)
  (e2: exp t (C.drop1 c ix) (C.get_index c ix)):
    Lemma
      (ensures bless_apps (subst1_apps' e1 ix e2) == subst1_apps' (bless_apps e1) ix (bless e2))
      (decreases e1) =
  match e1 with
  | XPrim p -> ()
  | XApp f e ->
    lemma_bless_distributes_subst_apps f ix e2;
    lemma_bless_distributes_subst e ix e2

let rec lemma_bless_of_bigstep (#t: table) (#c: context t) (#a: t.ty) (#streams: list (row c)) (#e: exp t c a) (#v: t.ty_sem a) (hBS: bigstep streams e v):
  Tot (bigstep streams (bless e) v)
    (decreases hBS) =
  admit ()

let rec lemma_bless_of_bigstep_always (#t: table) (#c: context t) (#streams: list (row c)) (#e: exp t c t.propty) (hB: bigstep_always streams e):
  Tot (bigstep_always streams (bless e))
    (decreases hB) =
  admit ()


let rec lemma_bigstep_always_of_bless (#t: table) (#c: context t) (#streams: list (row c)) (#e: exp t c t.propty) (hB: bigstep_always streams (bless e)):
  Tot (bigstep_always streams e)
    (decreases hB) =
  admit ()

let rec lemma_check_bless (#t: table) (#c: context t) (#a: t.ty) (#streams: list (row c)) (#e: exp t c a) (hC: check PM.check_mode_all streams e):
  Tot (check PM.check_mode_valid streams (bless e))
    (decreases hC) =
  match hC with
  | CkBase s b -> CkBase s b
  | CkApps s ea hCA -> CkApps s (bless_apps ea) (lemma_check_bless_apps hCA)
  | CkFby1 s v e1 -> CkFby1 s v (bless e1)
  | CkFbyS l p v e1 hC1 ->
    CkFbyS l p v _ (lemma_check_bless hC1)
  | CkMu s e1 hC1 ->
    lemma_bless_distributes_subst e1 0 (XMu e1);
    CkMu s (bless e1) (lemma_check_bless hC1)
  | CkLet s e1 e2 hC1 ->
    lemma_bless_distributes_subst e2 0 e1;
    CkLet s (bless e1) (bless e2) (lemma_check_bless hC1)
  | CkContract s ps r g i hR hG hCr hCig ->
    lemma_bless_distributes_subst g 0 i;

    let hCig': either (bigstep_always s (bless r) -> False) (check PM.check_mode_valid s (bless i) & check PM.check_mode_valid s (bless (subst1 g i))) =
      match hCig with
      | Inl hBN -> Inl (fun hB -> hBN (lemma_bigstep_always_of_bless hB))
      | Inr (hCi, hCg) -> Inr (lemma_check_bless hCi, lemma_check_bless hCg)
    in
    let hR' (pm: PM.prop_status_contains PM.check_mode_valid PM.PSValid) =
      lemma_bless_of_bigstep_always (hR pm)
    in
    let hG' (pm: PM.prop_status_contains PM.check_mode_valid PM.PSValid) (hB: bigstep_always s (bless r)) =
      lemma_bless_of_bigstep_always (hG pm (lemma_bigstep_always_of_bless hB))
    in
    CkContract #PM.check_mode_valid s PM.PSValid (bless r) (bless g) (bless i) hR' hG' (lemma_check_bless hCr) hCig'

  | CkCheck s ps e1 hC1 hB ->
    let hB' (pm: PM.prop_status_contains PM.check_mode_valid PM.PSValid) =
      lemma_bless_of_bigstep_always (hB pm)
    in
    CkCheck s PM.PSValid (bless e1) (lemma_check_bless hC1) hB'

and lemma_check_bless_apps (#t: table) (#c: context t) (#a: funty t.ty) (#streams: list (row c)) (#ea: exp_apps t c a) (hC: check_apps PM.check_mode_all streams ea):
  Tot (check_apps PM.check_mode_valid streams (bless_apps ea))
    (decreases hC)=
  match hC with
  | CkPrim s p -> CkPrim s p
  | CkApp s f e1 hCA hC1 ->
    CkApp s (bless_apps f) (bless e1)
      (lemma_check_bless_apps hCA)
      (lemma_check_bless hC1)


let lemma_check_all_bless (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a { check_all PM.check_mode_all e }):
  Lemma (ensures check_all PM.check_mode_valid (bless e))
    [SMTPat (check_all PM.check_mode_valid (bless e))] =
  introduce forall streams. check PM.check_mode_valid streams (bless e)
  with (
    eliminate forall streams. check PM.check_mode_all streams e with streams;
    bind_squash () (fun x -> return_squash (lemma_check_bless x))
  )
