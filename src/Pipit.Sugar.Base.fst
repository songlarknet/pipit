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

type s (t: table) (a: t.ty)  = m (exp t [] (t.ty_sem a))
type s' (t: table) (a: Type) = m (exp t [] a)

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
    (XVar x, s'))

let run (e: s' 't 'a) : exp 't [] 'a =
  let (a, _) = e { fresh = 0 } in
  a

let run1 (#a: ('t).ty) (f: s 't a -> s' 't 'b) : exp 't [a] 'b =
  let (ax, s) = fresh' a { fresh = 0 } in
  let a       = XVar ax in
  let (b,  s) = f (m_pure a) s in
  close1 b ax

let run2 (#a #b: ('t).ty) (f: s 't a -> s 't b -> s' 't 'c) : exp 't [a; b] 'c =
  let s       = { fresh = 0 } in
  let (ax, s) = fresh' a s in
  let (bx, s) = fresh' b s in
  let a       = XVar ax in
  let b       = XVar bx in
  let (c,  s) = f (m_pure a) (m_pure b) s in
  close1 (close1 c bx) ax

let let'
  (#a #b: ('t).ty)
  (e: s 't a)
  (f: s 't a -> s 't b):
    s 't b =
  (fun s ->
    let (xvar, s) = fresh' a s in
    let evar = XVar xvar in
    let (e, s) = e s in
    let (e', s) = f (m_pure evar) s in
    (XLet a e (close1 e' xvar), s))

let rec'
  (#a: ('t).ty)
  (f: s 't a -> s 't a):
    s 't a =
  (fun s ->
    let (xvar, s) = fresh' a s in
    let evar = XVar xvar in
    let (e', s) = f (m_pure evar) s in
    (XMu (close1 e' xvar), s))

let check'
  (#a: ('t).ty)
  (name: string)
  (e: s 't ('t).propty)
  (f: s 't a):
    s 't a =
  (fun s ->
    let (e, s) = e s in
    let (f, s) = f s in
    (XCheck name e f, s))

// XXX: this unit-check is dangerous, the check will disappear if the returned unit isn't mentioned in the result expression.
// I really want a monadic/effectful interface that collects a list of checks.
// when I tried this before I had trouble reifying effectful expressions inside
// tactics. need to work that out.
let check
  (name: string)
  (e: s 't ('t).propty):
    s 't ('t).propty =
  let' e (fun p -> check' name p p)

let pure (#a: ('t).ty) (v: ('t).ty_sem a): s 't a =
  m_pure (XVal v)

(* followed-by, initialised delay *)
let fby (#a: ('t).ty) (v: ('t).ty_sem a) (e: s 't a): s 't a = (fun s -> let (e, s) = e s in (XFby v e, s))

(* uninitialised delay, or default.
  this can be convenient, but it's kind of unsafe: we don't check that the
  default value is never used.
  we could imagine annotating it with a refinement of (false fby true…)
 *)
let pre (#a: ('t).ty) (e: s 't a): s 't a = fby (('t).val_default a) e

(* "p -> q" in Lustre, first element of p then remainder of q *)
let (-->) (#a: ('t).ty) (e1 e2: s 't a): s 't a =
  (fun s ->
    let (e1, s) = e1 s in
    let (e2, s) = e2 s in
    (XThen e1 e2, s))

// #push-options "--ifuel 0 --fuel 0"
let (<$>)
  (#a: ('t).ty)
  (#b: funty ('t).ty)
  (f: prim 't (FTFun a b))
  (e: s 't a):
      s' 't (funty_sem ('t).ty_sem b) =
  let sem = ('t).ty_sem in
  lemma_funty_sem_FTFun ('t).ty_sem a b;
  (fun s ->
    let (aa, s) = e s in
    (XApp (XPrim f) aa, s))

let (<*>)
  (f: s' 't ('a -> 'b))
  (e: s' 't 'a):
      s' 't 'b =
  (fun s ->
    let (f, s) = f s in
    let (a, s) = e s in
    (XApp f a, s))

let liftP1
  (#a #b: ('t).ty)
  (f: prim 't (FTFun a (FTVal b)))
  (e: s 't a):
      s 't b =
  f <$> e

let liftP2
  (#a #b #c: ('t).ty)
  (f: prim 't (FTFun a (FTFun b (FTVal c))))
  (a': s 't a)
  (b': s 't b):
       s 't c =
  f <$> a' <*> b'

let liftP3
  (#a #b #c #d: ('t).ty)
  (f: prim 't (FTFun a (FTFun b (FTFun c (FTVal d)))))
  (a': s 't a)
  (b': s 't b)
  (c': s 't c):
      s 't d =
  f <$> a' <*> b' <*> c'

