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
  XCB.lemma_sealed_of_bless true b;
  XCB.lemma_check_all_bless_contract r g b;
  // XCB.lemma_check_all_bless g;
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


let lemma_check_XBase
  (#t: table) (#c: context t) (#a: t.ty)
  (m: PM.check_mode)
  (b: exp_base t c a):
  Lemma (check_all m (XBase b))
    [SMTPat (check_all m (XBase b))]
    = admit ()

let lemma_check_XFby
  (#t: table) (#c: context t) (#a: t.ty)
  (m: PM.check_mode)
  (v: t.ty_sem a)
  (e: exp t c a { check_all m e }):
  Lemma (check_all m (XFby v e))
    [SMTPat (check_all m (XFby v e))]
    = admit ()

let lemma_check_XPrim
  (#t: table) (#c: context t)
  (m: PM.check_mode)
  (p: t.prim):
  Lemma (check_all_apps m (XPrim #t #c p))
    [SMTPat (check_all_apps m (XPrim #t #c p))]
    = admit ()

let lemma_check_XApp
  (#t: table) (#c: context t) (#arg: t.ty) (#res: funty t.ty)
  (m: PM.check_mode)
  (f: exp_apps t c (FTFun arg res) { check_all_apps m f })
  (e: exp      t c        arg      { check_all      m e }):
  Lemma (check_all_apps m (XApp f e))
    [SMTPat (check_all_apps m (XApp f e))]
    = admit ()

let lemma_check_XApps
  (#t: table) (#c: context t) (#arg: t.ty)
  (m: PM.check_mode)
  (f: exp_apps t c (FTVal arg) { check_all_apps m f }):
  Lemma (check_all m (XApps f))
    [SMTPat (check_all m (XApps f))]
    = admit ()

let lemma_check_XApp1
  (#t: table) (#c: context t) (#arg: t.ty) (#res: funty t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg res })
  (e: exp      t c        arg      { check_all      m e }):
  Lemma (check_all_apps m (XApp #t #c #arg #res (XPrim p) e))
    // [SMTPat (check_all_apps m (XApp f e))]
    = admit ()

let lemma_check_XApps1
  (#t: table) (#c: context t) (#arg #res: t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg (FTVal res) })
  (e: exp      t c        arg      { check_all      m e }):
  Lemma (check_all m (XApps #t #c #res (XApp (XPrim p) e)))
    // [SMTPat (check_all m (XApps #t #c #res (XApp (XPrim p) e)))]
    =
      lemma_check_XApp1 #t #c #arg #(FTVal res) m p e;
      admit ()

let lemma_check_XApps2
  (#t: table) (#c: context t) (#arg1 #arg2 #res: t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg1 (FTFun arg2 (FTVal res)) })
  (e1: exp      t c        arg1     { check_all      m e1 })
  (e2: exp      t c        arg2     { check_all      m e2 }):
  Lemma (check_all m (XApps #t #c #res (XApp (XApp (XPrim p) e1) e2)))
    // [SMTPat (check_all m (XApps #t #c #res (XApp (XPrim p) e)))]
    =
      lemma_check_XApp1 #t #c #arg1 #(FTFun arg2 (FTVal res)) m p e1;
      admit ()

let lemma_check_XApps3
  (#t: table) (#c: context t) (#arg1 #arg2 #arg3 #res: t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg1 (FTFun arg2 (FTFun arg3 (FTVal res))) })
  (e1: exp      t c        arg1     { check_all      m e1 })
  (e2: exp      t c        arg2     { check_all      m e2 })
  (e3: exp      t c        arg3     { check_all      m e3 }):
  Lemma (check_all m (XApps #t #c #res (XApp (XApp (XApp (XPrim p) e1) e2) e3)))
    // [SMTPat (check_all m (XApps #t #c #res (XApp (XPrim p) e)))]
    =
      // lemma_check_XApp1 #t #c #arg1 #(FTFun arg2 (FTFun arg3 (FTVal res))) m p e1;
      admit ()

// TODO:ADMIT: proofs, relatively simple
assume val lemma_check_XLet
  (#t: table) (#c: context t) (#a #b: t.ty)
  (m: PM.check_mode)
  (e1: exp t c a { check_all m e1 })
  (e2: exp t (a :: c) b { check_all m e2 }):
  Lemma (check_all m (XLet a e1 e2))
    [SMTPat (check_all m (XLet a e1 e2))]

assume val lemma_check_XMu
  (#t: table) (#c: context t) (#a: t.ty)
  (m: PM.check_mode)
  (e1: exp t (a :: c) a { check_all m e1 }):
  Lemma (check_all m (XMu e1))
    [SMTPat (check_all m (XMu e1))]

// assume val lemma_check_valid_XContract_unknown
//   (#t: table) (#c: context t) (#a: t.ty)
//   (er: exp t       c  t.propty { check_all PM.check_mode_valid er })
//   (eg: exp t (a :: c) t.propty { check_all PM.check_mode_valid eg })
//   (ei: exp t       c  a        { check_all PM.check_mode_valid ei }):
//   Lemma (check_all PM.check_mode_valid (XContract PM.contract_status_unknown er eg ei))
//     [SMTPat (check_all PM.check_mode_valid (XContract PM.contract_status_unknown er eg ei))]

assume val lemma_check_valid_XCheck_unknown
  (#t: table) (#c: context t)
  (e1: exp t c t.propty { check_all PM.check_mode_valid e1 }):
  Lemma (check_all PM.check_mode_valid (XCheck PM.PSUnknown e1))
    [SMTPat (check_all PM.check_mode_valid (XCheck PM.PSUnknown e1))]
