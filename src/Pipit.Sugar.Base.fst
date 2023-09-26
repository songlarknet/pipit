(* Base syntactic helpers for writing stream programs.
   This module provides a type constructor for streams `s t a` and combinators
   for combining them together; the stream type is parameterised by the primop
   table `t` and the result type `a` (which is a `t.ty`).
   There are `run`, `run1` and `run2` functions for converting stream programs
   to core expressions.
*)
module Pipit.Sugar.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Checked.Base
open Pipit.Exp.Checked.Compound

module C  = Pipit.Context.Base
module CX = Pipit.Exp.Checked.Compound
module PM = Pipit.Prop.Metadata

(**** Internal types ****)
type _state = {
  fresh: nat;
}

type _m      (a: Type)                  = _state -> (a & _state)
type _s_apps (t: table) (a: funty t.ty) = _m (cexp_apps t [] a)

(**** Exposed types: s for stream ****)
type s       (t: table) (a: t.ty)       = _m (cexp      t [] a)
type prim    (t: table) (ty: funty t.ty)= p: t.prim { t.prim_ty p == ty }

(**** Internal combinators ****)

let _purem (#a: Type) (x: a): _m a =
  fun s -> (x, s)

let _freshm (#ty: eqtype) (t: ty): _m (C.var t) =
  fun s ->
    let x = s.fresh in
    (C.Var x), { fresh = x + 1 }

let _freshs (t: table) (ty: t.ty): s t ty =
  fun s ->
    let (x, s') = _freshm ty s in
    (XBase (XVar x), s')

let run0 (#t: table) (#ty: t.ty) (e: s t ty) : cexp t [] ty =
  let (a, _) = e { fresh = 0 } in
  a

(**** Top-level / integration combinators ****)
let run1 (#t: table) (#a #b: t.ty) (f: s t a -> s t b) : cexp t [a] b =
  let (ax, s) = _freshm a { fresh = 0 } in
  let a       = XBase (XVar ax) in
  let (b,  s) = f (_purem a) s in
  CX.close1 b ax

let run2 (#a #b #c: ('t).ty) (f: s 't a -> s 't b -> s 't c) : cexp 't [a; b] c =
  let s       = { fresh = 0 } in
  let (ax, s) = _freshm a s in
  let (bx, s) = _freshm b s in
  let a       = XBase (XVar ax) in
  let b       = XBase (XVar bx) in
  let (c,  s) = f (_purem a) (_purem b) s in
  CX.close1 (CX.close1 c bx) ax

let reflect1 (#t: table) (#a #b: t.ty) (e: cexp t [a] b) (sa: s t a): s t b =
  fun s ->
    let (ax, s) = sa s in
    (XLet a ax e, s)

let reflect2 (#t: table) (#a #b #c: t.ty) (e: cexp t [a; b] c) (sa: s t a) (sb: s t b): s t c =
  fun s ->
    let (ax, s) = sa s in
    let (bx, s) = sb s in
    (XLet b bx (XLet a (CX.weaken [b] ax) e), s)

(**** Top-level / integration combinators ****)
let let'
  (#a #b: ('t).ty)
  (e: s 't a)
  (f: s 't a -> s 't b):
    s 't b =
  (fun s ->
    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (e, s)    = e s in
    let (e', s)   = f (_purem evar) s in
    (XLet a e (CX.close1 e' xvar), s))

let rec'
  (#a: ('t).ty)
  (f: s 't a -> s 't a):
    s 't a =
  (fun s ->
    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (e', s)   = f (_purem evar) s in
    (XMu (CX.close1 e' xvar), s))

// XXX: this unit-check is dangerous, the check will disappear if the returned unit isn't mentioned in the result expression.
// I really want a monadic/effectful interface that collects a list of checks.
// when I tried this before I had trouble reifying effectful expressions inside
// tactics. need to work that out.
let check
  (e: s 't ('t).propty):
    s 't ('t).propty =
  (fun s ->
    let (e, s) = e s in
    (XCheck PM.PSUnknown e, s))

let check'
  (#a: ('t).ty)
  (e: s 't ('t).propty)
  (f: s 't a):
    s 't a =
  let' (check e) (fun _ -> f)

noeq
type _contract (t: table) (a: t.ty) = {
  rely: s t t.propty;
  guar: (s t a -> s t t.propty);
  impl: s t a;
}

let contract
  (#a: ('t).ty)
  (c: _contract 't a):
    s 't a =
  (fun s ->
    let (r, s)    = c.rely s in
    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (g, s)    = c.guar (_purem evar) s in
    let g         = CX.close1 g xvar in
    let (i, s)    = c.impl s in
    (XContract PM.contract_status_unknown r g i, s))


let pure (#a: ('t).ty) (v: ('t).ty_sem a): s 't a =
  _purem (XBase (XVal v))

(* followed-by, initialised delay *)
let fby (#a: ('t).ty) (v: ('t).ty_sem a) (e: s 't a): s 't a = (fun s -> let (e, s) = e s in (XFby v e, s))

(* uninitialised delay, or default.
  this can be convenient, but it's kind of unsafe: we don't check that the
  default value is never used.
  we could imagine annotating it with a refinement of (false fby true…)
 *)
let pre (#a: ('t).ty) (e: s 't a): s 't a = fby (('t).val_default a) e

(* "p -> q" in Lustre, first element of p then remainder of q *)
// XXX: needs ifthenelse primitive (if (true fby false) then e1 else e2)
// let (-->) (#a: ('t).ty) (e1 e2: s 't a): s 't a =
//   (fun s ->
//     let (e1, s) = e1 s in
//     let (e2, s) = e2 s in
//     (XThen e1 e2, s))

// #push-options "--ifuel 0 --fuel 0"

let liftP1
  (#a #b: ('t).ty)
  (f: prim 't (FTFun a (FTVal b)))
  (e: s 't a):
      s 't b =
  (fun s ->
    let (aa, s) = e s in
    CX.lemma_check_XApps1 #'t #[] #a #b PM.check_mode_valid f aa;
    (XApps (XApp (XPrim f) aa), s))

let liftP2
  (#a #b #c: ('t).ty)
  (f: prim 't (FTFun a (FTFun b (FTVal c))))
  (ea: s 't a)
  (eb: s 't b):
       s 't c =
  (fun s ->
    let (aa, s) = ea s in
    let (bb, s) = eb s in
    CX.lemma_check_XApps2 #'t #[] #a #b #c PM.check_mode_valid f aa bb;
    (XApps (XApp (XApp (XPrim f) aa) bb), s))

let liftP3
  (#a #b #c #d: ('t).ty)
  (f: prim 't (FTFun a (FTFun b (FTFun c (FTVal d)))))
  (ea: s 't a)
  (eb: s 't b)
  (ec: s 't c):
       s 't d =
  (fun s ->
    let (aa, s) = ea s in
    let (bb, s) = eb s in
    let (cc, s) = ec s in
    CX.lemma_check_XApps3 #'t #[] #a #b #c #d PM.check_mode_valid f aa bb cc;
    (XApps (XApp (XApp (XApp (XPrim f) aa) bb) cc), s))

