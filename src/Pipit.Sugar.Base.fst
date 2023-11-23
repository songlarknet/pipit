(* Base syntactic helpers for writing stream programs.
   This module provides a type constructor for streams `stream t a` and combinators
   for combining them together; the stream type is parameterised by the primop
   table `t` and the result type `a` (which is a `t.ty`).
   There are `run`, `run1` and `run2` functions for converting stream programs
   to core expressions.

  The definitions in this module are declared to be opaque-to-SMT, as the
  higher-order representation is expensive to encode in the SMT solver. When we
  want to reason about actual programs, we don't want to use this higher-order
  representation, and instead use the normalizer to go to transition systems or
  explicit expressions. So, hiding these from the SMT solver seems to help
  reduce the clutter in the environment.

*)
module Pipit.Sugar.Base

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Checked.Base
open Pipit.Exp.Checked.Compound

module C  = Pipit.Context.Base
module CX = Pipit.Exp.Checked.Compound
module PM = Pipit.Prop.Metadata

irreducible
let stream_ctor_attr = ()

(**** Internal types ****)
type _state = {
  fresh: nat;
}

type _m      (a: Type)                  = _state -> (a & _state)
type _s_apps (t: table u#i u#j) (a: funty t.ty) = _m (cexp_apps t [] a)

(**** Exposed types: delayed streams and primitives ****)
[@@stream_ctor_attr]
type stream  (t: table u#i u#j) (a: t.ty)       = _m (cexp      t [] a)
type prim    (t: table u#i u#j) (ty: funty t.ty)= p: t.prim { t.prim_ty p == ty }

(**** Internal combinators ****)

[@@"opaque_to_smt"]
let _purem (#a: Type) (x: a): _m a =
  fun s -> (x, s)

[@@"opaque_to_smt"]
let _freshm (#ty: Type) (t: ty): _m (C.var t) =
  fun s ->
    let x = s.fresh in
    (C.Var x), { fresh = x + 1 }

[@@"opaque_to_smt"]
let _freshs (t: table) (ty: t.ty): stream t ty =
  fun s ->
    let (x, s') = _freshm ty s in
    (XBase (XVar x), s')

(**** Top-level / integration combinators ****)
[@@"opaque_to_smt"]
let exp_of_stream0 (#t: table) (#ty: t.ty) (e: stream t ty) : cexp t [] ty =
  let (a, _) = e { fresh = 0 } in
  a

[@@"opaque_to_smt"]
let exp_of_stream1 (#t: table) (#a #b: t.ty) (f: stream t a -> stream t b) : cexp t [a] b =
  let (ax, s) = _freshm a { fresh = 0 } in
  let a       = XBase (XVar ax) in
  let (b,  s) = f (_purem a) s in
  CX.close1 b ax

[@@"opaque_to_smt"]
let exp_of_stream2 (#a #b #c: ('t).ty) (f: stream 't a -> stream 't b -> stream 't c) : cexp 't [a; b] c =
  let s       = { fresh = 0 } in
  let (ax, s) = _freshm a s in
  let (bx, s) = _freshm b s in
  let a       = XBase (XVar ax) in
  let b       = XBase (XVar bx) in
  let (c,  s) = f (_purem a) (_purem b) s in
  CX.close1 (CX.close1 c bx) ax

[@@"opaque_to_smt"]
let exp_of_stream3 (#a #b #c #d: ('t).ty) (f: stream 't a -> stream 't b -> stream 't c -> stream 't d) : cexp 't [a; b; c] d =
  let s       = { fresh = 0 } in
  let (ax, s) = _freshm a s in
  let (bx, s) = _freshm b s in
  let (cx, s) = _freshm c s in
  let a       = XBase (XVar ax) in
  let b       = XBase (XVar bx) in
  let c       = XBase (XVar cx) in
  let (d,  s) = f (_purem a) (_purem b) (_purem c) s in
  CX.close1 (CX.close1 (CX.close1 d cx) bx) ax

[@@"opaque_to_smt"]
let stream_of_exp0 (#t: table) (#a: t.ty) (e: cexp t [] a): stream t a =
  fun s ->
    (e, s)

[@@"opaque_to_smt"]
let stream_of_exp1 (#t: table) (#a #b: t.ty) (e: cexp t [a] b) (sa: stream t a): stream t b =
  fun s ->
    let (ax, s) = sa s in
    (XLet a ax e, s)

[@@"opaque_to_smt"]
let stream_of_exp2 (#t: table) (#a #b #c: t.ty) (e: cexp t [a; b] c) (sa: stream t a) (sb: stream t b): stream t c =
  fun s ->
    let (ax, s) = sa s in
    let (bx, s) = sb s in
    (XLet b bx (XLet a (CX.weaken [b] ax) e), s)

[@@"opaque_to_smt"]
let stream_of_exp3 (#t: table) (#a #b #c #d: t.ty) (e: cexp t [a; b; c] d) (sa: stream t a) (sb: stream t b) (sc: stream t c): stream t d =
  fun s ->
    let (ax, s) = sa s in
    let (bx, s) = sb s in
    let (cx, s) = sc s in
    (XLet c cx (XLet b (CX.weaken [c] bx) (XLet a (CX.weaken [b; c] ax) e)), s)

(**** Binding combinators ****)
[@@"opaque_to_smt"]
let let'
  (#a #b: ('t).ty)
  (e: stream 't a)
  (f: stream 't a -> stream 't b):
    stream 't b =
  (fun s ->
    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (e, s)    = e s in
    let (e', s)   = f (_purem evar) s in
    (XLet a e (CX.close1 e' xvar), s))

[@@"opaque_to_smt"]
let rec'
  (#a: ('t).ty)
  (f: stream 't a -> stream 't a):
    stream 't a =
  (fun s ->
    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (e', s)   = f (_purem evar) s in
    (XMu (CX.close1 e' xvar), s))

[@@"opaque_to_smt"]
let (let^) (#a #b: ('t).ty) (f: stream 't a) (g: stream 't a -> stream 't b) =
    let' f g

// XXX: this unit-check is dangerous, the check will disappear if the returned unit isn't mentioned in the result expression.
// I really want a monadic/effectful interface that collects a list of checks.
// when I tried this before I had trouble reifying effectful expressions inside
// tactics. need to work that out.
[@@"opaque_to_smt"]
let check
  (e: stream 't ('t).propty):
    stream 't ('t).propty =
  (fun s ->
    let (e, s) = e s in
    (XCheck PM.PSUnknown e, s))

[@@"opaque_to_smt"]
let const (#a: ('t).ty) (v: ('t).ty_sem a): stream 't a =
  _purem (XBase (XVal v))

(* followed-by, initialised delay *)
[@@"opaque_to_smt"]
let fby (#a: ('t).ty) (v: ('t).ty_sem a) (e: stream 't a): stream 't a = (fun s -> let (e, s) = e s in (XFby v e, s))

(* uninitialised delay, or default.
  this can be convenient, but it's kind of unsafe: we don't check that the
  default value is never used.
  we could imagine annotating it with a refinement of (false fby true…)
 *)
[@@"opaque_to_smt"]
let pre (#a: ('t).ty) (e: stream 't a): stream 't a = fby (('t).val_default a) e

(* "p -> q" in Lustre, first element of p then remainder of q *)
// XXX: needs ifthenelse primitive (if (true fby false) then e1 else e2)
// let (->^) (#a: ('t).ty) (e1 e2: s 't a): s 't a =
//   (fun s ->
//     let (e1, s) = e1 s in
//     let (e2, s) = e2 s in
//     (XThen e1 e2, s))

// #push-options "--ifuel 0 --fuel 0"

[@@"opaque_to_smt"]
let liftP'prim
  (#ft: funty ('t).ty)
  (f: prim 't ft):
      _s_apps 't ft =
  (fun s -> (XPrim f, s))

[@@"opaque_to_smt"]
let liftP'app
  (#a: ('t).ty)
  (#ft: funty ('t).ty)
  (f: _s_apps 't (FTFun a ft))
  (ea: stream 't a):
      _s_apps 't ft =
  (fun s ->
    let (ff, s) = f s in
    let (aa, s) = ea s in
    (XApp ff aa, s))

[@@"opaque_to_smt"]
let (<*>)
  (#a: ('t).ty)
  (#ft: funty ('t).ty)
  (f: _s_apps 't (FTFun a ft))
  (ea: stream 't a):
      _s_apps 't ft = liftP'app f ea

[@@"opaque_to_smt"]
let liftP'apps
  (#a: ('t).ty)
  (ea: _s_apps 't (FTVal a)):
      stream 't a =
  (fun s ->
    let (aa, s) = ea s in
    (XApps aa, s))

[@@"opaque_to_smt"]
let liftP1
  (#a #b: ('t).ty)
  (f: prim 't (FTFun a (FTVal b)))
  (e: stream 't a):
      stream 't b =
    liftP'apps (liftP'prim f <*> e)

[@@"opaque_to_smt"]
let liftP2
  (#a #b #c: ('t).ty)
  (f: prim 't (FTFun a (FTFun b (FTVal c))))
  (ea: stream 't a)
  (eb: stream 't b):
       stream 't c =
    liftP'apps (liftP'prim f <*> ea <*> eb)

[@@"opaque_to_smt"]
let liftP3
  (#a #b #c #d: ('t).ty)
  (f: prim 't (FTFun a (FTFun b (FTFun c (FTVal d)))))
  (ea: stream 't a)
  (eb: stream 't b)
  (ec: stream 't c):
       stream 't d =
    liftP'apps (liftP'prim f <*> ea <*> eb <*> ec)

