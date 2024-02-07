(* Translating between Pipit.Exp checked semantics and system invariants *)
module Pipit.System.Exp.Check.Invariants

open Pipit.Prim.Table
open Pipit.Exp.Base
open Pipit.System.Exp.Check.Base

open FStar.Squash

module SXCA = Pipit.System.Exp.Check.Assumptions
module SXCO = Pipit.System.Exp.Check.Obligations

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties
module SI  = Pipit.System.Ind

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality
module XK  = Pipit.Exp.Checked.Base

module PM = Pipit.Prop.Metadata

module T    = FStar.Tactics

#push-options "--split_queries always"

let rec check_base_nil
  (#t: table) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (e: exp t c a { XC.causal e }):
  Lemma
    (ensures (
      XK.check mode [] e
    ))
    (decreases e)
    =
  match e with
  | XBase _ -> ()
  | XApps ea ->
    check_base_apps_nil mode ea
  | XFby v e1 ->
    check_base_nil mode e1
  | XMu e1 ->
    check_base_nil mode e1
  | XLet b e1 e2 ->
    check_base_nil mode e1;
    check_base_nil mode e2
  | XCheck ps e1 ->
    check_base_nil mode e1
  | XContract ps er eg eb ->
    check_base_nil mode er;
    check_base_nil mode eg;
    check_base_nil mode eb

and check_base_apps_nil
  (#t: table) (#c: context t) (#a: funty t.ty)
  (mode: PM.check_mode)
  (e: exp_apps t c a { XC.causal_apps e }):
  Lemma
    (ensures (
      XK.check_apps mode [] e
    ))
    (decreases e)
    =
  match e with
  | XPrim _ -> ()
  | XApp f e ->
    check_base_apps_nil mode f;
    check_base_nil mode e


let rec check_invariant_of_check_base
  (#t: table) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (rows: list (row c))
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      XK.check mode rows e
    ))
    (ensures (
      check_invariant mode rows e
    ))
    (decreases e)
    =
  match e with
  | XBase _ -> ()
  | XApps ea ->
    check_invariant_of_check_base_apps mode rows ea
  | XFby v e1 ->
    check_invariant_of_check_base mode rows e1
  | XMu e1 ->
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows (XMu e1)) rows in
    check_invariant_of_check_base mode rows' e1
  | XLet b e1 e2 ->
    check_invariant_of_check_base  mode rows e1;
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows e1) rows in
    check_invariant_of_check_base  mode rows' e2
  | XCheck ps e1 ->
    check_invariant_of_check_base  mode rows e1
  | XContract ps er eg eb ->
    check_invariant_of_check_base mode rows er;
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows eb) rows in
    introduce XB.bigstep_always rows er ==> check_invariant mode rows' eg
    with pf. check_invariant_of_check_base mode rows' eg;
    ()
and check_invariant_of_check_base_apps
  (#t: table) (#c: context t) (#a: funty t.ty)
  (mode: PM.check_mode)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e }):
  Lemma
    (requires (
      XK.check_apps mode rows e
    ))
    (ensures (
      check_apps_invariant mode rows e
    ))
    (decreases e)
    =
  match e with
  | XPrim _ -> ()
  | XApp f e ->
    check_invariant_of_check_base_apps mode rows f;
    check_invariant_of_check_base mode rows e


let rec check_of_sealed
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      XK.check PM.check_mode_valid rows e /\
      XK.sealed false e
    ))
    (ensures (
      XK.check PM.check_mode_unknown rows e
    ))
    (decreases e)
    =
  match e with
  | XBase _ -> ()
  | XApps ea ->
    check_apps_of_sealed rows ea
  | XFby v e1 ->
    check_of_sealed rows e1
  | XMu e1 ->
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows (XMu e1)) rows in
    check_of_sealed rows' e1;
    introduce forall (vs: list (t.ty_sem a) { XB.bigsteps_prop rows (XMu e1) vs }).
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) e1
    with
      XB.bigsteps_deterministic_squash rows (XMu e1) vs (XC.lemma_bigsteps_total_vs rows (XMu e1));
    ()
  | XLet b e1 e2 ->
    check_of_sealed rows e1;
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows e1) rows in
    check_of_sealed rows' e2;
    introduce forall (vs: list (t.ty_sem b) { XB.bigsteps_prop rows e1 vs }).
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) e2
    with
      XB.bigsteps_deterministic_squash rows e1 vs (XC.lemma_bigsteps_total_vs rows e1);
    ()
  | XCheck ps e1 ->
    check_of_sealed rows e1;
    ()
  | XContract ps er eg eb ->
    check_of_sealed rows er;
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows eb) rows in
    assert (XB.bigstep_always rows' eg);
    check_of_sealed rows eb;
    check_of_sealed rows' eg;
    introduce forall (vs: list (t.ty_sem a) { XB.bigsteps_prop rows eb vs }).
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) eg
    with
      XB.bigsteps_deterministic_squash rows eb vs (XC.lemma_bigsteps_total_vs rows eb);
    ()

and check_apps_of_sealed
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e }):
  Lemma
    (requires (
      XK.check_apps PM.check_mode_valid rows e /\
      XK.sealed_apps false e
    ))
    (ensures (
      XK.check_apps PM.check_mode_unknown rows e
    ))
    (decreases e)
    =
  match e with
  | XPrim _ -> ()
  | XApp f e ->
    check_apps_of_sealed rows f;
    check_of_sealed rows e


let rec check_base_unknown_of_check_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e }):
  Lemma
    (requires (
      XK.check PM.check_mode_valid rows e /\
      XK.sealed true e /\
      check_invariant PM.check_mode_unknown rows e
    ))
    (ensures (
      XK.check PM.check_mode_unknown rows e
    ))
    (decreases e)
    =
  match e with
  | XBase _ -> ()
  | XApps ea ->
    check_base_unknown_of_check_invariant_apps rows ea
  | XFby v e1 ->
    check_base_unknown_of_check_invariant rows e1
  | XMu e1 ->
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows (XMu e1)) rows in
    assert (XK.check PM.check_mode_valid rows' e1);
    assert (check_invariant PM.check_mode_unknown rows' e1);

    check_base_unknown_of_check_invariant rows' e1;

    introduce forall (vs: list (t.ty_sem a) { XB.bigsteps_prop rows (XMu e1) vs }).
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) e1
    with
      XB.bigsteps_deterministic_squash rows (XMu e1) vs (XC.lemma_bigsteps_total_vs rows (XMu e1));

    ()

  | XLet b e1 e2 ->
    check_base_unknown_of_check_invariant rows e1;
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows e1) rows in
    assert (XK.check PM.check_mode_valid rows' e2);
    assert (check_invariant PM.check_mode_unknown rows' e2);
    check_base_unknown_of_check_invariant rows' e2;

    introduce forall (vs: list (t.ty_sem b) { XB.bigsteps_prop rows e1 vs }).
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) e2
    with
      XB.bigsteps_deterministic_squash rows e1 vs (XC.lemma_bigsteps_total_vs rows e1);

    ()

  | XCheck ps e1 ->
    check_base_unknown_of_check_invariant rows e1
  | XContract ps er eg eb ->
    assert (XB.bigstep_always rows er);
    check_base_unknown_of_check_invariant rows er;
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows eb) rows in
    check_base_unknown_of_check_invariant rows' eg;

    introduce forall (vs: list (t.ty_sem a) { XB.bigsteps_prop rows eb vs }).
      XK.check PM.check_mode_unknown (CR.extend1 vs rows) eg
    with
      XB.bigsteps_deterministic_squash rows eb vs (XC.lemma_bigsteps_total_vs rows eb);
    check_of_sealed rows eb;
    ()


and check_base_unknown_of_check_invariant_apps
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e }):
  Lemma
    (requires (
      XK.check_apps PM.check_mode_valid rows e /\
      XK.sealed_apps true e /\
      check_apps_invariant PM.check_mode_unknown rows e
    ))
    (ensures (
      XK.check_apps PM.check_mode_unknown rows e
    ))
    (decreases e)
    =
  match e with
  | XPrim _ -> ()
  | XApp f e ->
    check_base_unknown_of_check_invariant_apps rows f;
    check_base_unknown_of_check_invariant rows e
