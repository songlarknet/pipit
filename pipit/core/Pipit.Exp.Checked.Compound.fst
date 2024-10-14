(* Validated expressions

  These are used by the desugaring phase.
  They are currently trusted, ie not proved.
  Most of them should be *able* to be verified, but just haven't been yet.
  The close1 lemma can't currently be verified, though: it says that replacing
  a free variable with a bound variable doesn't affect the checked semantics.
  But, free variables currently have no bigstep semantics, so we can't check
  programs with free variables in them.
  The solution is to amend the bigstep semantics to take some kind of values
  for the free variables as well.
*)
module Pipit.Exp.Checked.Compound

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding
open Pipit.Exp.Causality
open Pipit.Exp.Checked.Base
module XCB = Pipit.Exp.Checked.Bless

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties
module PM = Pipit.Prop.Metadata

type cexp (t: table u#i u#j) (c: context t) (a: t.ty) = e: exp t c a { check_all PM.check_mode_valid e /\ sealed true e }
type cexp_apps (t: table u#i u#j) (c: context t) (a: funty t.ty) = e: exp_apps t c a { check_all_apps PM.check_mode_valid e /\ sealed_apps true e }

let bless (#a: ('t).ty) (#c: context 't) (e: cexp 't c a { check_all PM.check_mode_unknown e }): cexp 't c a =
  let e' = bless e in
  XCB.lemma_sealed_of_bless true e;
  XCB.lemma_check_all_bless e;
  e'


let bless_contract (#a: ('t).ty) (#c: context 't) (r: cexp 't c ('t).propty) (g: cexp 't (a :: c) ('t).propty) (b: cexp 't c a { contract_valid r g b }): cexp 't c a =
  let rely = r in
  let guar = Pipit.Exp.Checked.Base.bless g in
  let body = Pipit.Exp.Checked.Base.bless b in
  let e' = XContract PM.PSUnknown rely guar body in
  XCB.lemma_sealed_of_bless true g;
  XCB.lemma_sealed_of_bless false b;
  XCB.lemma_check_all_bless_contract r g b;
  e'


(* Cannot yet prove this:
  this is used in the syntactic sugar, but not in the semantics.
*)
let close1 (#a #b: ('t).ty) (#c: context 't) (e: cexp 't c a) (x: C.var b): cexp 't (b :: c) a =
  let e' = close1 e x in
  // AXIOM:ADMIT lemma close1 preserves validity
  coerce_eq (admit ()) e'

(* Substitution does not preserve the "sealed-ness" of expressions: it could
  introduce unknown properties inside contracts, which wouldn't be proved by
  the (abstract) transition systems. *)
// let subst1 (#a #b: ('t).ty) (#c: context 't) (e: cexp 't (b :: c) a) (payload: cexp 't c b): cexp 't c a =

let weaken (#c c': context 't) (#a: ('t).ty) (e: cexp 't c a): Tot (cexp 't (C.append c c') a) =
  let e' = weaken c' e in
  // TODO:ADMIT lemma weaken preserves validity
  coerce_eq (admit ()) e'
