(* Validated expressions
*)
module Pipit.Exp.Checked.Compound

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Binding
open Pipit.Exp.Causality
open Pipit.Exp.Checked.Base

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties
module PM = Pipit.Prop.Metadata

type cexp (t: table) (c: context t) (a: t.ty) = e: exp t c a { check' PM.check_mode_valid e }
type cexp_apps (t: table) (c: context t) (a: funty t.ty) = e: exp_apps t c a { check_apps' PM.check_mode_valid e }

let close1 (#a #b: ('t).ty) (#c: context 't) (e: cexp 't c a) (x: C.var b): cexp 't (b :: c) a =
  let e' = close1 e x in
  // TODO:ADMIT lemma close1 preserves validity
  coerce_eq (admit ()) e'

let subst1 (#a #b: ('t).ty) (#c: context 't) (e: cexp 't (b :: c) a) (payload: cexp 't c b): cexp 't c a =
  let e' = subst1 e payload in
  // TODO:ADMIT lemma subst1 preserves validity
  coerce_eq (admit ()) e'

let weaken (#c c': context 't) (#a: ('t).ty) (e: cexp 't c a): Tot (cexp 't (C.append c c') a) =
  let e' = weaken c' e in
  // TODO:ADMIT lemma weaken preserves validity
  coerce_eq (admit ()) e'


let lemma_check_XBase
  (#t: table) (#c: context t) (#a: t.ty)
  (m: PM.check_mode)
  (b: exp_base t c a):
  Lemma (check' m (XBase b))
    // [SMTPat (check' m (XBase b))]
    = ()

let lemma_check_XPrim
  (#t: table) (#c: context t)
  (m: PM.check_mode)
  (p: t.prim):
  Lemma (check_apps' m (XPrim #t #c p))
    // [SMTPat (check_apps' m (XPrim #t #c p))]
    = ()

let lemma_check_XApp
  (#t: table) (#c: context t) (#arg: t.ty) (#res: funty t.ty)
  (m: PM.check_mode)
  (f: exp_apps t c (FTFun arg res) { check_apps' m f })
  (e: exp      t c        arg      { check'      m e }):
  Lemma (check_apps' m (XApp f e))
    // [SMTPat (check_apps' m (XApp f e))]
    = ()

let lemma_check_XApps
  (#t: table) (#c: context t) (#arg: t.ty) (#res: funty t.ty)
  (m: PM.check_mode)
  (f: exp_apps t c (FTVal arg) { check_apps' m f }):
  Lemma (check' m (XApps f))
    // [SMTPat (check_apps' m (XApp f e))]
    = ()

let lemma_check_XApp1
  (#t: table) (#c: context t) (#arg: t.ty) (#res: funty t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg res })
  (e: exp      t c        arg      { check'      m e }):
  Lemma (check_apps' m (XApp #t #c #arg #res (XPrim p) e))
    // [SMTPat (check_apps' m (XApp f e))]
    = ()

let lemma_check_XApps1
  (#t: table) (#c: context t) (#arg #res: t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg (FTVal res) })
  (e: exp      t c        arg      { check'      m e }):
  Lemma (check' m (XApps #t #c #res (XApp (XPrim p) e)))
    // [SMTPat (check' m (XApps #t #c #res (XApp (XPrim p) e)))]
    =
      lemma_check_XApp1 #t #c #arg #(FTVal res) m p e;
      ()

let lemma_check_XApps2
  (#t: table) (#c: context t) (#arg1 #arg2 #res: t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg1 (FTFun arg2 (FTVal res)) })
  (e1: exp      t c        arg1     { check'      m e1 })
  (e2: exp      t c        arg2     { check'      m e2 }):
  Lemma (check' m (XApps #t #c #res (XApp (XApp (XPrim p) e1) e2)))
    // [SMTPat (check' m (XApps #t #c #res (XApp (XPrim p) e)))]
    =
      lemma_check_XApp1 #t #c #arg1 #(FTFun arg2 (FTVal res)) m p e1;
      ()

let lemma_check_XApps3
  (#t: table) (#c: context t) (#arg1 #arg2 #arg3 #res: t.ty)
  (m: PM.check_mode)
  (p: t.prim { t.prim_ty p == FTFun arg1 (FTFun arg2 (FTFun arg3 (FTVal res))) })
  (e1: exp      t c        arg1     { check'      m e1 })
  (e2: exp      t c        arg2     { check'      m e2 })
  (e3: exp      t c        arg3     { check'      m e3 }):
  Lemma (check' m (XApps #t #c #res (XApp (XApp (XApp (XPrim p) e1) e2) e3)))
    // [SMTPat (check' m (XApps #t #c #res (XApp (XPrim p) e)))]
    =
      // lemma_check_XApp1 #t #c #arg1 #(FTFun arg2 (FTFun arg3 (FTVal res))) m p e1;
      admit ()

// TODO:ADMIT: proofs, relatively simple
assume val lemma_check_XLet
  (#t: table) (#c: context t) (#a #b: t.ty)
  (m: PM.check_mode)
  (e1: exp t c a { check' m e1 })
  (e2: exp t (a :: c) b { check' m e2 }):
  Lemma (check' m (XLet a e1 e2))
    [SMTPat (check' m (XLet a e1 e2))]

assume val lemma_check_XMu
  (#t: table) (#c: context t) (#a: t.ty)
  (m: PM.check_mode)
  (e1: exp t (a :: c) a { check' m e1 }):
  Lemma (check' m (XMu e1))
    [SMTPat (check' m (XMu e1))]

// assume val lemma_check_valid_XContract_unknown
//   (#t: table) (#c: context t) (#a: t.ty)
//   (er: exp t       c  t.propty { check' PM.check_mode_valid er })
//   (eg: exp t (a :: c) t.propty { check' PM.check_mode_valid eg })
//   (ei: exp t       c  a        { check' PM.check_mode_valid ei }):
//   Lemma (check' PM.check_mode_valid (XContract PM.contract_status_unknown er eg ei))
//     [SMTPat (check' PM.check_mode_valid (XContract PM.contract_status_unknown er eg ei))]

assume val lemma_check_valid_XCheck_unknown
  (#t: table) (#c: context t)
  (e1: exp t c t.propty { check' PM.check_mode_valid e1 }):
  Lemma (check' PM.check_mode_valid (XCheck PM.PSUnknown e1))
    [SMTPat (check' PM.check_mode_valid (XCheck PM.PSUnknown e1))]
