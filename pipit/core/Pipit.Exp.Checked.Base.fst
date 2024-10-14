(* Checked expressions: expressions that are known to satisfy properties
*)
module Pipit.Exp.Checked.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module PM = Pipit.Prop.Metadata

module XC = Pipit.Exp.Causality

(* Check an expression under given mode and environment *)
let rec check (#t: table u#i u#j) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (rows: list (row c))
  (e: exp t c a)
  : Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps ea ->
    check_apps mode rows ea
  | XFby v e1 ->
    check mode rows e1
  | XMu e1 ->
    // Extend environment to include recursive value of e1; check subexpression
    forall (vs: list (t.ty_sem a) { bigsteps_prop rows (XMu e1) vs }).
      check mode (CR.extend1 vs rows) e1
  | XLet b e1 e2 ->
    // Check e1, then use e1's values to check e2
    check mode rows e1 /\
    (forall (vs: list (t.ty_sem b) { bigsteps_prop rows e1 vs}).
      check mode (CR.extend1 vs rows) e2)
  | XCheck ps e1 ->
    // Check that property evaluates to trues.
    // We also check inside the property. Although it seems odd that properties
    // can include more properties, it can happen after inlining.
    check mode rows e1 /\
    (PM.prop_status_contains mode ps ==>
      bigstep_always rows e1)
  | XContract ps rely guar body ->
    // Contract instantiation:
    // The property status is used to delay checking the caller.
    // When checking the caller, the rely must be trues.
    (PM.prop_status_contains mode ps ==>
      bigstep_always rows rely) /\
    // Check rely subexpression
    check mode rows rely /\
    // Contract definition assumes rely is trues:
    (bigstep_always rows rely ==>
      (forall (vs: list (t.ty_sem a) { bigsteps_prop rows body vs}).
        // If rely and we are in contract-check-definition mode, then guarantee is trues
        bigstep_always (CR.extend1 vs rows) guar /\
        // If rely is trues and any mode, then check sub-properties of guar
        check mode (CR.extend1 vs rows) guar /\
        // If rely is trues and any mode, then check sub-properties of body
        check mode rows body))

and check_apps (#t: table) (#c: context t) (#a: funty t.ty)
  (mode: PM.check_mode)
  (rows: list (row c))
  (e: exp_apps t c a)
  : Tot prop (decreases e) =
  match e with
  | XPrim p -> True
  | XApp ef ea ->
    check_apps mode rows ef /\
    check      mode rows ea


let check_all (#t: table u#i u#j) (#c: context t) (#a: t.ty) (mode: PM.check_mode) (e: exp t c a): prop =
  forall (streams: list (row c)).
    check mode streams e

let check_all_apps (#t: table u#i u#j) (#c: context t) (#a: funty t.ty) (mode: PM.check_mode) (e: exp_apps t c a): prop =
  forall (streams: list (row c)).
    check_apps mode streams e

let contract_valid (#t: table u#i u#j) (#c: context t) (#a: t.ty)
  (rely: exp t c t.propty) (guar: exp t (a::c) t.propty) (body: exp t c a): prop =
  forall (streams: list (row c)).
  forall (vs: list (t.ty_sem a) { bigsteps_prop streams body vs }).
  check PM.check_mode_valid streams rely ==>
  check PM.check_mode_valid streams body ==>
  check PM.check_mode_valid (CR.extend1 vs streams) guar ==>
  bigstep_always streams rely ==>
    // We don't need to check unknown properties in the rely: they will be
    // checked at instantiation time.
    (// check PM.check_mode_unknown streams rely /\
    check PM.check_mode_unknown streams body /\
    check PM.check_mode_unknown (CR.extend1 vs streams) guar /\
    bigstep_always (CR.extend1 vs streams) guar)


(* Check that an expression is "sealed", in that it contains no unknown
  properties. When verifying properties via transition system, we do not allow
  contract instances with unknown properties inside them, though unknown
  properties can occur outside of contracts.
  When generating executable code, we should not allow unknown properties at
  all, although this check is not yet implemented. *)
let rec sealed (#t: table u#i u#j) (#c: context t) (#a: t.ty)
  (allow_unknowns: bool)
  (e: exp t c a)
  : Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps ea ->
    sealed_apps allow_unknowns ea
  | XFby v e1 -> sealed allow_unknowns e1
  | XMu e1 -> sealed allow_unknowns e1
  | XLet b e1 e2 -> sealed allow_unknowns e1 /\ sealed allow_unknowns e2
  | XCheck ps e1 -> (ps == PM.PSUnknown ==> allow_unknowns) /\ sealed allow_unknowns e1
  | XContract ps rely guar body ->
    (ps == PM.PSUnknown ==> allow_unknowns) /\
    sealed allow_unknowns rely /\ sealed allow_unknowns guar /\ sealed false body

and sealed_apps (#t: table) (#c: context t) (#a: funty t.ty)
  (allow_unknowns: bool)
  (e: exp_apps t c a)
  : Tot prop (decreases e) =
  match e with
  | XPrim p -> True
  | XApp ef ea ->
    sealed_apps allow_unknowns ef /\ sealed allow_unknowns ea

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
