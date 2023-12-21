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
module CB = Pipit.Exp.CollectBinds
module PM = Pipit.Prop.Metadata

irreducible
let stream_ctor_attr = ()

(**** Note: disable CSE:
  I have disabled CSE because it complicates the normalisation required to
  extract in Network.TTCan.Extract. We may need to optimise the representation.
*)

(**** Internal types ****)
noeq
type _state (t: table) = {
  fresh: nat;
  // See note: disable CSE
  // binds: list (CB.bind t);
}

let _state0 (t: table): _state t = { fresh = 0; } // binds = []; }

type _m      (t: table) (a: Type)       = _state t -> (a & _state t)
type _s_apps (t: table) (a: funty t.ty) = _m t (cexp_apps t [] a)

(**** Exposed types: delayed streams and primitives ****)
type stream  (t: table) (a: t.ty)       = _m t (cexp      t [] a)
type prim    (t: table) (ty: funty t.ty)= p: t.prim { t.prim_ty p == ty }

(**** Internal combinators ****)

[@@"opaque_to_smt"]
let _purem (#t: table) (#a: Type) (x: a): _m t a =
  fun s -> (x, s)

[@@"opaque_to_smt"]
let _freshm (#t: table) (ty: t.ty): _m t (C.var ty) =
  fun s ->
    let x = s.fresh in
    C.Var x, { s with fresh = x + 1 }

[@@"opaque_to_smt"]
let _freshs (#t: table) (ty: t.ty): stream t ty =
  fun s ->
    let (x, s) = _freshm ty s in
    (XBase (XVar x), s)

(*See note: disable CSE*)
// [@@"opaque_to_smt"]
// let _mk_bind (#t: table) (#ty: t.ty) (def: cexp t [] ty): stream t ty =
//   fun s ->
//     let open CB in
//     match find_equivalent s.binds def with
//     | None ->
//       let (x, s) = _freshm ty s in
//       let binds  = { bind_ty = ty; bind_var = x; bind_expr = def } :: s.binds in
//       (XBase (XVar x), { s with binds = binds })
//     | Some x ->
//       (XBase (XVar x), s)

[@@"opaque_to_smt"]
let _mk_let (#t: table) (#ty1 #ty2: t.ty) (def: cexp t [] ty1) (body: cexp t [ty1] ty2): _m t (cexp t [] ty2) =
  fun s ->
    (*See note: disable CSE*)
    // let (def', s) = _mk_bind def s in
    // (CX.subst1 body def', s)
    let e: cexp t [] ty2 = XLet _ def body in
    (e, s)

(*See note: disable CSE*)
// [@@"opaque_to_smt"]
// let _take_dependent_lets (#t: table) (#ty #ty': t.ty) (body: cexp t [] ty) (xvar: C.var ty'): stream t ty =
//   fun s ->
//     let (here, later) = CB.dependent_binds s.binds [C.Var?.v xvar] in
//     (CB.binds_to_lets here body, { s with binds = later })

[@@"opaque_to_smt"]
let _exp_of_stream (#t: table) (#ty: t.ty) (e: stream t ty) (s: _state t): cexp t [] ty =
  let (a, s) = e s in
  (*See note: disable CSE*)
  // let b      = CB.binds_to_lets s.binds a in
  // b
  a


[@@"opaque_to_smt"]
let _exp_of_streamS (#t: table) (#a #b: t.ty) (#c: context t) (#rem: Type)
  (g: rem -> _state t -> cexp t c b)
  (f: stream t a -> rem)
  (s: _state t)
    : cexp t (a :: c) b =
  let (ax, s) = _freshm a s in
  let a       = XBase (XVar ax) in
  let astrm   = _purem a in
  let rem     = f astrm in
  let expb    = g rem s in
  CX.close1 expb ax

(**** Top-level / integration combinators ****)
[@@"opaque_to_smt"]
let exp_of_stream0 (#t: table) (#ty: t.ty) (e: stream t ty) : cexp t [] ty =
  _exp_of_stream e (_state0 t)


[@@"opaque_to_smt"]
let exp_of_stream1 (#t: table) (#a #b: t.ty) (f: stream t a -> stream t b) : cexp t [a] b =
  _exp_of_streamS _exp_of_stream f (_state0 t)

[@@"opaque_to_smt"]
let exp_of_stream2 (#a #b #c: ('t).ty) (f: stream 't a -> stream 't b -> stream 't c) : cexp 't [a; b] c =
  _exp_of_streamS (_exp_of_streamS _exp_of_stream) f (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream3 (#a #b #c #d: ('t).ty) (f: stream 't a -> stream 't b -> stream 't c -> stream 't d) : cexp 't [a; b; c] d =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream)) f (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream4 (#a #b #c #d #e: ('t).ty) (f: stream 't a -> stream 't b -> stream 't c -> stream 't d -> stream 't e) : cexp 't [a; b; c; d] e =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream))) f (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream5 (#a #b #c #d #e #f: ('t).ty) (fn: stream 't a -> stream 't b -> stream 't c -> stream 't d -> stream 't e -> stream 't f) : cexp 't [a; b; c; d; e] f =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream)))) fn (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream6 (#a #b #c #d #e #f #g: ('t).ty) (fn: stream 't a -> stream 't b -> stream 't c -> stream 't d -> stream 't e -> stream 't f -> stream 't g) : cexp 't [a; b; c; d; e; f] g =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream))))) fn (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream7 (#a #b #c #d #e #f #g #h: ('t).ty) (fn: stream 't a -> stream 't b -> stream 't c -> stream 't d -> stream 't e -> stream 't f -> stream 't g -> stream 't h) : cexp 't [a; b; c; d; e; f; g] h =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream)))))) fn (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream8 (#a #b #c #d #e #f #g #h #i: ('t).ty) (fn: stream 't a -> stream 't b -> stream 't c -> stream 't d -> stream 't e -> stream 't f -> stream 't g -> stream 't h -> stream 't i) : cexp 't [a; b; c; d; e; f; g; h] i =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream))))))) fn (_state0 't)

[@@"opaque_to_smt"]
let exp_of_stream9 (#a #b #c #d #e #f #g #h #i #j: ('t).ty) (fn: stream 't a -> stream 't b -> stream 't c -> stream 't d -> stream 't e -> stream 't f -> stream 't g -> stream 't h -> stream 't i -> stream 't j) : cexp 't [a; b; c; d; e; f; g; h; i] j =
  _exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS (_exp_of_streamS _exp_of_stream)))))))) fn (_state0 't)


[@@"opaque_to_smt"]
let stream_of_exp0 (#t: table) (#a: t.ty) (e: cexp t [] a): stream t a =
  fun s ->
    (e, s)

[@@"opaque_to_smt"]
let stream_of_exp1 (#t: table) (#a #b: t.ty) (e: cexp t [a] b) (sa: stream t a): stream t b =
  fun s ->
    let (ax, s) = sa s in
    (*See note: disable CSE*)
    // let (ax, s) = _mk_bind ax s in
    // (CX.subst1 e ax, s)
    (XLet a ax e, s)

[@@"opaque_to_smt"]
let stream_of_exp2 (#t: table) (#a #b #c: t.ty) (e: cexp t [a; b] c) (sa: stream t a) (sb: stream t b): stream t c =
  fun s ->
    let (ax, s) = sa s in
    // let (ax, s) = _mk_bind ax s in
    let (bx, s) = sb s in
    // let (bx, s) = _mk_bind bx s in
    let ex = XLet b bx (XLet a (CX.weaken [b] ax) e) in
    // let ex = CX.subst1 (CX.subst1 e (CX.weaken [b] ax)) bx in
    (ex, s)

[@@"opaque_to_smt"]
let stream_of_exp3 (#t: table) (#a #b #c #d: t.ty) (e: cexp t [a; b; c] d) (sa: stream t a) (sb: stream t b) (sc: stream t c): stream t d =
  fun s ->
    let (ax, s) = sa s in
    // let (ax, s) = _mk_bind ax s in
    let (bx, s) = sb s in
    // let (bx, s) = _mk_bind bx s in
    let (cx, s) = sc s in
    // let (cx, s) = _mk_bind cx s in
    // let ex      = CX.subst1 (CX.subst1 (CX.subst1 e (CX.weaken [b; c] ax)) (CX.weaken [c] bx)) cx in
    let ex = XLet c cx (XLet b (CX.weaken [c] bx) (XLet a (CX.weaken [b; c] ax) e)) in
    (ex, s)

(**** Binding combinators ****)
[@@"opaque_to_smt"]
let let'
  (#a #b: ('t).ty)
  (e: stream 't a)
  (f: stream 't a -> stream 't b):
    stream 't b =
  (fun s ->
    let (e, s)    = e s in
    (*See note: disable CSE*)
    // let (e, s)    = _mk_bind e s in
    // let (e', s)   = f (_purem e) s in
    // (e', s))

    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (e', s)   = f (_purem evar) s in
    let e' = XLet a e (CX.close1 e' xvar) in
    (e', s))

[@@"opaque_to_smt"]
let rec'
  (#a: ('t).ty)
  (f: stream 't a -> stream 't a):
    stream 't a =
  (fun s ->
    let (xvar, s) = _freshm a s in
    let evar      = XBase (XVar xvar) in
    let (e', s)   = f (_purem evar) s in
    //Disable CSE: let (e', s)   = _take_dependent_lets e' xvar s in
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
    stream 't ('t).unitty =
  (fun s ->
    let (e, s) = e s in
    (XCheck PM.PSUnknown e, s))

[@@"opaque_to_smt"]
let const (#a: ('t).ty) (v: ('t).ty_sem a): stream 't a =
  _purem (XBase (XVal v))

(* followed-by, initialised delay *)
[@@"opaque_to_smt"]
let fby (#a: ('t).ty) (v: ('t).ty_sem a) (e: stream 't a): stream 't a =
  (fun s ->
    let (e, s) = e s in (XFby v e, s))

(* uninitialised delay, or default.
  this can be convenient, but it's kind of unsafe: we don't check that the
  default value is never used.
  we could imagine annotating it with a refinement of (false fby true…)
 *)
[@@"opaque_to_smt"]
let pre (#a: ('t).ty) (e: stream 't a): stream 't a = fby (('t).val_default a) e

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

