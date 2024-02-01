module Pipit.Exp.Checked.Properties

open Pipit.Exp.Checked.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding

module C  = Pipit.Context.Base
module PM = Pipit.Prop.Metadata

open FStar.Squash


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

// let rec lemma_bigstep_always_of_bless (#t: table) (#c: context t) (streams: list (row c)) (e: exp t c t.propty):
//   Lemma
//     (requires (bigstep_always streams (bless e)))
//     (ensures (bigstep_always streams e))
//     (decreases streams) =
//   match streams with
//   | [] -> ()
//   | _ :: s' ->
//     //ADMIT:easy, apply determinism or implement other direction of lemma_bless_of_bigstep
//     admit ()

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

    assert (bigstep_always s r);
    lemma_bless_of_bigstep_always s r;
    lemma_bless_of_bigstep_always s (subst1 g i);

    let hCig': either (~ (bigstep_always s (bless r))) (check PM.check_mode_valid s (bless i) & check PM.check_mode_valid s (bless (subst1 g i))) =
      match hCig with
      | Inl hBN -> false_elim ()
      | Inr (hCi, hCg) -> Inr (lemma_check_bless hCi, lemma_check_bless hCg)
    in

    CkContract #PM.check_mode_valid s PM.PSValid (bless r) (bless g) (bless i) () () (lemma_check_bless hCr) hCig'

  | CkCheck s ps e1 hC1 hB ->
    lemma_bless_of_bigstep_always s e1;
    CkCheck s PM.PSValid (bless e1) (lemma_check_bless hC1) ()

and lemma_check_bless_apps (#t: table) (#c: context t) (#a: funty t.ty) (#streams: list (row c)) (#ea: exp_apps t c a) (hC: check_apps PM.check_mode_all streams ea):
  Tot (check_apps PM.check_mode_valid streams (bless_apps ea))
    (decreases hC)=
  match hC with
  | CkPrim s p -> CkPrim s p
  | CkApp s f e1 hCA hC1 ->
    CkApp s (bless_apps f) (bless e1)
      (lemma_check_bless_apps hCA)
      (lemma_check_bless hC1)


let lemma_check_all_bless (#t: table u#i u#j) (#c: context t) (#a: t.ty) (e: exp t c a { check_all PM.check_mode_all e }):
  Lemma (ensures check_all PM.check_mode_valid (bless e))
    [SMTPat (check_all PM.check_mode_valid (bless e))] =
  introduce forall streams.
    check_prop PM.check_mode_valid streams (bless e)
  with (

    assert (check_prop PM.check_mode_all streams e);
    // norm_spec [delta_only [`%check_prop]] (check_prop PM.check_mode_all streams e);
    assert (squash (check PM.check_mode_all streams e))
       by (FStar.Tactics.dump "X");
      // ;
    bind_squash () (fun (x : check PM.check_mode_all streams e) -> return_squash (lemma_check_bless x))
  )
