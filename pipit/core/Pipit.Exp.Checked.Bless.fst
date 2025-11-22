(* Properties about blessing *)
module Pipit.Exp.Checked.Bless

open Pipit.Exp.Checked.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module PM = Pipit.Prop.Metadata

module List = FStar.List.Tot

open FStar.Squash

#set-options "--fuel 1 --ifuel 1 --split_queries always"

(*** Bindings and substitution ***)
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

(*** Bigstep properties ***)
let rec lemma_bless_of_bigstep (#t: table) (#c: context t) (#a: t.ty) (#streams: list (row c)) (#e: exp t c a) (#v: t.ty_sem a) (hBS: bigstep streams e v):
  Tot (bigstep streams (bless e) v)
    (decreases hBS) =
  match hBS with
  | BSBase s xb v b -> BSBase s xb v b
  | BSApps s ea v hBA ->
    BSApps s (bless_apps ea) v (lemma_bless_of_bigstep_apps hBA)
  | BSFby1 s v e -> BSFby1 s v (bless e)
  | BSFbyS l p v0 v' e hB -> BSFbyS l p v0 v' (bless e) (lemma_bless_of_bigstep hB)
  | BSMu s e1 v hB ->
    lemma_bless_distributes_subst e1 0 (XMu e1);
    BSMu s (bless e1) v (lemma_bless_of_bigstep hB)
  | BSLet s e1 e2 v hB ->
    lemma_bless_distributes_subst e2 0 e1;
    BSLet s (bless e1) (bless e2) v (lemma_bless_of_bigstep hB)
  | BSContract s ps r g i v hB ->
    BSContract s PM.PSValid (bless r) (bless g) (bless i) v (lemma_bless_of_bigstep hB)
  | BSCheck s ps e1 v hB ->
    BSCheck s PM.PSValid (bless e1) v (lemma_bless_of_bigstep hB)

and lemma_bless_of_bigstep_apps (#t: table) (#c: context t) (#a: funty t.ty) (#streams: list (row c)) (#e: exp_apps t c a) (#v: funty_sem t.ty_sem a) (hBS: bigstep_apps streams e v):
  Tot (bigstep_apps streams (bless_apps e) v)
    (decreases hBS) =
  match hBS with
  | BSPrim s p -> BSPrim s p
  | BSApp s f e fv ev hBA hB ->
    BSApp s _ _ _ _
      (lemma_bless_of_bigstep_apps hBA)
      (lemma_bless_of_bigstep hB)


let rec lemma_bigstep_of_bless (#t: table) (#c: context t) (#a: t.ty) (#streams: list (row c)) (#e: exp t c a) (#v: t.ty_sem a) (hBS: bigstep streams (bless e) v):
  Tot (bigstep streams e v)
    (decreases hBS) =
  match e with
  | XBase xb ->
    let BSBase _ _ _ xb = hBS in
    BSBase _ _ _ xb
  | XApps ea ->
    let BSApps s _ v hBA = hBS in
    BSApps s ea v (lemma_bigstep_of_bless_apps hBA)
  | XFby v e1 ->
    (match hBS with
    | BSFby1 s v _ ->
      BSFby1 s v e1
    | BSFbyS l p v0 v' _ hB ->
      BSFbyS l p v0 v' e1 (lemma_bigstep_of_bless hB))
  | XMu e1 ->
    let BSMu s _ v hB = hBS in
    lemma_bless_distributes_subst e1 0 (XMu e1);
    BSMu s e1 v (lemma_bigstep_of_bless hB)
  | XLet b e1 e2 ->
    let BSLet s _ _ v hB = hBS in
    lemma_bless_distributes_subst e2 0 e1;
    BSLet s e1 e2 v (lemma_bigstep_of_bless hB)
  | XCheck ps e1 ->
    let BSCheck s _ _ v hB = hBS in
    BSCheck s ps e1 v (lemma_bigstep_of_bless hB)
  | XContract ps er eg eb ->
    let BSContract s _ _ _ _ v hB = hBS in
    BSContract s ps er eg eb v (lemma_bigstep_of_bless hB)

and lemma_bigstep_of_bless_apps (#t: table) (#c: context t) (#a: funty t.ty) (#streams: list (row c)) (#e: exp_apps t c a) (#v: funty_sem t.ty_sem a) (hBS: bigstep_apps streams (bless_apps e) v):
  Tot (bigstep_apps streams e v)
    (decreases hBS) =
  match e with
  | XPrim p -> BSPrim streams p
  | XApp f e ->
    let BSApp s _ _ fv ev hBA hB = hBS in
    BSApp s f e _ _
      (lemma_bigstep_of_bless_apps hBA)
      (lemma_bigstep_of_bless hB)


let rec lemma_bless_of_bigstep_always (#t: table) (#c: context t) (streams: list (row c)) (e: exp t c t.propty):
  Lemma
    (requires (bigstep_always streams e))
    (ensures (bigstep_always streams (bless e)))
    (decreases streams) =
  match streams with
  | [] -> ()
  | s :: s' ->
    let hB: squash (bigstep (s :: s') e true) = () in
    let hB: squash (bigstep streams (bless e) true) =
      (bind_squash hB (fun hB -> return_squash (lemma_bless_of_bigstep hB)))
    in
    lemma_bless_of_bigstep_always s' e;
    ()

let rec lemma_bigsteps_of_bless (#t: table) (#c: context t) (#a: t.ty)
  (streams: list (row c))
  (e: exp t c a)
  (vs: list (t.ty_sem a))
  (hBS: bigsteps streams (bless e) vs)
  : Tot (bigsteps streams e vs) (decreases hBS)
  = match hBS with
  | BSs0 _ -> BSs0 e
  | BSsS rows _ vs row v hBSs hBS1 ->
    let hBSs' = lemma_bigsteps_of_bless rows e vs hBSs in
    let hBS1' = lemma_bigstep_of_bless hBS1 in
    BSsS rows e vs row v hBSs' hBS1'


let lemma_bigsteps_prop_of_bless (#t: table) (#c: context t) (#a: t.ty)
  (streams: list (row c))
  (e: exp t c a)
  (vs: list (t.ty_sem a)):
  Lemma
    (requires (
      bigsteps_prop streams (bless e) vs
    ))
    (ensures (
      bigsteps_prop streams e vs
    ))
    =
    bind_squash () (fun (hB: (bigsteps streams (bless e) vs)) ->
      return_squash (lemma_bigsteps_of_bless streams e vs hB))

(*** Checked semantics properties ***)
let rec lemma_check_bless (#t: table) (#c: context t) (#a: t.ty) (streams: list (row c)) (e: exp t c a):
  Lemma
    (requires (
      check PM.check_mode_valid streams e /\
      check PM.check_mode_unknown streams e
    ))
    (ensures (
      check PM.check_mode_valid streams (bless e)
    ))
    (decreases e) =
  admit ()
  (* TODO:ADMIT:update to latest F* 20251116 *)
  // match e with
  // | XBase b -> ()
  // | XApps ea -> lemma_check_bless_apps streams ea
  // | XFby v e1 -> lemma_check_bless streams e1
  // | XMu e1 ->
  //   introduce forall (vs: list (t.ty_sem a) { bigsteps_prop streams (XMu (bless e1)) vs }). check PM.check_mode_valid (CR.extend1 vs streams) (bless e1)
  //   with (
  //     lemma_bigsteps_prop_of_bless streams (XMu e1) vs;
  //     lemma_check_bless (CR.extend1 vs streams) e1
  //   )
  // | XLet b e1 e2 ->
  //   lemma_check_bless streams e1;
  //   introduce forall (vs: list (t.ty_sem b) { bigsteps_prop streams (bless e1) vs }). check PM.check_mode_valid (CR.extend1 vs streams) (bless e2)
  //   with (
  //     lemma_bigsteps_prop_of_bless streams e1 vs;
  //     lemma_check_bless (CR.extend1 vs streams) e2
  //   )
  // | XCheck ps e1 ->
  //   lemma_check_bless streams e1;
  //   lemma_bless_of_bigstep_always streams e1

  // | XContract ps er eg eb ->
  //   lemma_bless_of_bigstep_always streams er;
  //   lemma_check_bless streams er;

  //   introduce forall (vs: list (t.ty_sem a) { bigsteps_prop streams (bless eb) vs }).
  //     bigstep_always (CR.extend1 vs streams) (bless eg) /\
  //     check PM.check_mode_valid (CR.extend1 vs streams) (bless eg) /\
  //     check PM.check_mode_valid streams (bless eb)
  //   with (
  //     lemma_bigsteps_prop_of_bless streams eb vs;
  //     lemma_bless_of_bigstep_always (CR.extend1 vs streams) eg;
  //     lemma_check_bless (CR.extend1 vs streams) eg;
  //     lemma_check_bless streams eb;
  //     ()
  //   )


and lemma_check_bless_apps (#t: table) (#c: context t) (#a: funty t.ty) (streams: list (row c)) (ea: exp_apps t c a):
  Lemma
    (requires (
      check_apps PM.check_mode_valid streams ea /\
      check_apps PM.check_mode_unknown streams ea
    ))
    (ensures (
      check_apps PM.check_mode_valid streams (bless_apps ea)
    ))
    (decreases ea) =
  match ea with
  | XPrim f -> ()
  | XApp f e ->
    lemma_check_bless_apps streams f;
    lemma_check_bless streams e


let lemma_check_all_bless (#t: table u#i u#j) (#c: context t) (#a: t.ty) (e: exp t c a { check_all PM.check_mode_valid e /\ check_all PM.check_mode_unknown e }):
  Lemma (ensures check_all PM.check_mode_valid (bless e)) =
  introduce forall streams.
    check PM.check_mode_valid streams (bless e)
  with (
    lemma_check_bless streams e
  )

let lemma_check_all_bless_contract (#t: table u#i u#j) (#c: context t) (#a: t.ty)
  (r: exp t       c  t.propty { check_all PM.check_mode_valid r })
  (g: exp t (a :: c) t.propty { check_all PM.check_mode_valid g })
  (b: exp t       c  a        { check_all PM.check_mode_valid b /\ contract_valid r g b })
  :
  Lemma (ensures check_all PM.check_mode_valid (XContract PM.PSUnknown r (bless g) (bless b))) =
  introduce forall rows.
    (PM.prop_status_contains PM.check_mode_valid PM.PSUnknown ==> bigstep_always rows r) /\
    check PM.check_mode_valid rows r /\
    (bigstep_always rows r ==>
      (forall (vs: list (t.ty_sem a) { bigsteps_prop rows (bless b) vs}).
        (PM.prop_status_contains PM.check_mode_valid PM.PSValid ==>
          bigstep_always (CR.extend1 vs rows) (bless g)) /\
        check PM.check_mode_valid (CR.extend1 vs rows) (bless g) /\
        check PM.check_mode_valid rows (bless b)))
  with (
    introduce bigstep_always rows r ==>
      (forall (vs: list (t.ty_sem a) { bigsteps_prop rows (bless b) vs}).
        (PM.prop_status_contains PM.check_mode_valid PM.PSValid ==>
          bigstep_always (CR.extend1 vs rows) (bless g)) /\
        check PM.check_mode_valid (CR.extend1 vs rows) (bless g) /\
        check PM.check_mode_valid rows (bless b))
    with pf. (
      introduce forall (vs: list (t.ty_sem a) { bigsteps_prop rows (bless b) vs}).
        bigstep_always (CR.extend1 vs rows) (bless g) /\
        check PM.check_mode_valid (CR.extend1 vs rows) (bless g) /\
        check PM.check_mode_valid rows (bless b)
      with (
        lemma_bigsteps_prop_of_bless rows b vs;
        assert (bigstep_always (CR.extend1 vs rows) g);
        lemma_check_bless rows b;
        lemma_check_bless (CR.extend1 vs rows) g;
        lemma_bless_of_bigstep_always (CR.extend1 vs rows) g
      )
    )
  )


(*** Sealed ***)
let rec lemma_sealed_of_bless (#t: table) (#c: context t) (#a: t.ty)
  (opts: bool)
  (e: exp t c a)
  : Lemma (ensures sealed opts (bless e))
    (decreases e) =
  match e with
  | XBase _ -> ()
  | XApps ea -> lemma_sealed_of_bless_apps opts ea
  | XFby v e1' -> lemma_sealed_of_bless opts e1'
  | XMu e1' ->
    lemma_sealed_of_bless opts e1'
  | XLet b e1' e2' ->
    lemma_sealed_of_bless opts e1';
    lemma_sealed_of_bless opts e2'
  | XCheck s e1' ->
    lemma_sealed_of_bless opts e1'
  | XContract s r g b ->
    lemma_sealed_of_bless opts r;
    lemma_sealed_of_bless opts g;
    lemma_sealed_of_bless false b

and lemma_sealed_of_bless_apps (#t: table) (#c: context t) (#t1: funty t.ty)
  (opts: bool)
  (e1: exp_apps t c t1):
    Lemma
      (ensures sealed_apps opts (bless_apps e1))
      (decreases e1) =
  match e1 with
  | XPrim p -> ()
  | XApp f e ->
    lemma_sealed_of_bless_apps opts f;
    lemma_sealed_of_bless opts e
