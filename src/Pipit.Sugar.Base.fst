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
open Pipit.Exp.Binding

module C  = Pipit.Context.Base

type state = {
  fresh: nat;
}

type m (a: Type) =
  s: state -> (a & state)

type s (t: table) (a: t.ty)  = m (exp t [] a)
type s' (t: table) (a: funty t.ty)  = m (exp_apps t [] a)

type prim (t: table) (ty: funty t.ty) = p: t.prim { t.prim_ty p == ty }


let m_pure (#a: Type) (x: a): m a =
  fun s -> (x, s)

let fresh' (#ty: eqtype) (t: ty): m (C.var t) =
  (fun s ->
    let x = s.fresh in
    (C.Var x), { fresh = x + 1 })

let fresh (t: table) (ty: t.ty): s t ty =
  (fun s ->
    let (x, s') = fresh' ty s in
    (XBase (XVar x), s'))

let run (#t: table) (#ty: t.ty) (e: s t ty) : exp t [] ty =
  let (a, _) = e { fresh = 0 } in
  a

let run1 (#t: table) (#a #b: t.ty) (f: s t a -> s t b) : exp t [a] b =
  let (ax, s) = fresh' a { fresh = 0 } in
  let a       = XBase (XVar ax) in
  let (b,  s) = f (m_pure a) s in
  close1 b ax

let run2 (#a #b #c: ('t).ty) (f: s 't a -> s 't b -> s 't c) : exp 't [a; b] c =
  let s       = { fresh = 0 } in
  let (ax, s) = fresh' a s in
  let (bx, s) = fresh' b s in
  let a       = XBase (XVar ax) in
  let b       = XBase (XVar bx) in
  let (c,  s) = f (m_pure a) (m_pure b) s in
  close1 (close1 c bx) ax

let let'
  (#a #b: ('t).ty)
  (e: s 't a)
  (f: s 't a -> s 't b):
    s 't b =
  (fun s ->
    let (xvar, s) = fresh' a s in
    let evar = XBase (XVar xvar) in
    let (e, s) = e s in
    let (e', s) = f (m_pure evar) s in
    (XLet a e (close1 e' xvar), s))

let rec'
  (#a: ('t).ty)
  (f: s 't a -> s 't a):
    s 't a =
  (fun s ->
    let (xvar, s) = fresh' a s in
    let evar = XBase (XVar xvar) in
    let (e', s) = f (m_pure evar) s in
    (XMu (close1 e' xvar), s))

// XXX: this unit-check is dangerous, the check will disappear if the returned unit isn't mentioned in the result expression.
// I really want a monadic/effectful interface that collects a list of checks.
// when I tried this before I had trouble reifying effectful expressions inside
// tactics. need to work that out.
let check
  (name: string)
  (e: s 't ('t).propty):
    s 't ('t).propty =
  (fun s ->
    let (e, s) = e s in
    (XCheck name e, s))

let check'
  (#a: ('t).ty)
  (name: string)
  (e: s 't ('t).propty)
  (f: s 't a):
    s 't a =
  let' (check name e) (fun _ -> f)

let pure (#a: ('t).ty) (v: ('t).ty_sem a): s 't a =
  m_pure (XBase (XVal v))

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
    (XApps (XApp (XApp (XApp (XPrim f) aa) bb) cc), s))

