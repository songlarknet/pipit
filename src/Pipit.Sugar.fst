(* Syntactic sugar for writing nice-ish stream programs.
   This module provides a type constructor for streams `s 'a` and combinators
   for combining them together.
   There are `run`, `run1` and `run2` functions for converting stream programs
   to core expressions, but these should really be hidden...
*)
module Pipit.Sugar

open Pipit.Exp.Base
open Pipit.Exp.Binding
open Pipit.Inhabited

module C = Pipit.Context

module Pure = FStar.Monotonic.Pure

type state = {
  fresh: nat;
}

type m (a: Type) =
  s: state -> (a & state)

type s (a: Type) = m (exp [] a)

let m_pure (#a: Type) (x: a): m a =
  fun s -> (x, s)

let fresh' (t: Type): m (C.var t) =
  (fun s ->
    let x = s.fresh in
    (C.Var x), { fresh = x + 1 })

let fresh (t: Type): s t =
  (fun s ->
    let (x, s') = fresh' t s in
    (XVar x, s'))

let run (e: s 'a) : exp [] 'a =
  let (a, _) = e { fresh = 0 } in
  a

let run1 (f: s 'a -> s 'b) : exp ['a] 'b =
  let (ax, s) = fresh' 'a { fresh = 0 } in
  let a       = XVar ax in
  let (b,  s) = f (m_pure a) s in
  close1 b ax

let run2 (f: s 'a -> s 'b -> s 'c) : exp ['a; 'b] 'c =
  let s       = { fresh = 0 } in
  let (ax, s) = fresh' 'a s in
  let (bx, s) = fresh' 'b s in
  let a       = XVar ax in
  let b       = XVar bx in
  let (c,  s) = f (m_pure a) (m_pure b) s in
  close1 (close1 c bx) ax

let let'
  (e: s 'a)
  (f: s 'a -> s 'b):
    s 'b =
  (fun s ->
    let (xvar, s) = fresh' 'a s in
    let evar = XVar xvar in
    let (e, s) = e s in
    let (e', s) = f (m_pure evar) s in
    (XLet 'a e (close1 e' xvar), s))

let rec'
  {| inhabited 'a |}
  (f: s 'a -> s 'a):
    s 'a =
  (fun s ->
    let (xvar, s) = fresh' 'a s in
    let evar = XVar xvar in
    let (e', s) = f (m_pure evar) s in
    (XMu (close1 e' xvar), s))

let check'
  (name: string)
  (e: s bool)
  (f: s 'a):
    s 'a =
  (fun s ->
    let (e, s) = e s in
    let (f, s) = f s in
    (XCheck name e f, s))

let check
  (name: string)
  (e: s bool):
    s unit =
  check' name e (m_pure (XVal ()))

let pure (a: 'a): s 'a =
  m_pure (XVal a)

let (<$>)
  (f: ('a -> 'b))
  (a: s 'a):
      s 'b =
  (fun s ->
    let (a, s) = a s in
    (XApp (XVal f) a, s))

let (<*>)
  (f: s ('a -> 'b))
  (a: s 'a):
      s 'b =
  (fun s ->
    let (f, s) = f s in
    let (a, s) = a s in
    (XApp f a, s))

let liftA1
  (f: ('a -> 'b))
  (a: s 'a):
      s 'b =
  f <$> a

let liftA2
  (f: ('a -> 'b -> 'c))
  (a: s 'a)
  (b: s 'b):
      s 'c =
  f <$> a <*> b

let liftA3
  (f: ('a -> 'b -> 'c -> 'd))
  (a: s 'a)
  (b: s 'b)
  (c: s 'c):
      s 'd =
  f <$> a <*> b <*> c

let tt: s bool = pure true
let ff: s bool = pure false

let z (i: int): s int = pure i
let z0 = z 0
let z1 = z 1

(* Working with booleans *)
let (/\) = liftA2 (fun x y -> if x then y else false)
let (\/) = liftA2 (fun x y -> if x then true else y)
let (=>) = liftA2 (fun x y -> if x then y else true)

let op_Negation = liftA1 not
let (!^) = liftA1 not
let not_ = liftA1 not

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) (#t: eqtype) (a b: s t): s bool = liftA2 (fun x y -> x = y) a b

let (<>^) (#t: eqtype) (a b: s t): s bool = !^ (a =^ b)

let (+^) = liftA2 (+)
let (-^) = liftA2 (fun x y -> x - y)

let (/^) = liftA2 (/)
let ( *^ ) = liftA2 Prims.op_Multiply

let (<=^) = liftA2 (<=)
let (>=^) = liftA2 (>=)
let (<^) = liftA2 (<)
let (>^) = liftA2 (>)

let tup = liftA2 (fun a b -> (a,b))

let negate = liftA1 (fun x -> -x)

let if_then_else_impl (p: bool) (x y: 'a): 'a =
  if p then x else y

(* if-then-else *)
let ite = liftA3 if_then_else_impl
let if_then_else = ite

(* itialised delay *)
let fby (a: 'a) (e: s 'a): s 'a = (fun s -> let (e, s) = e s in (XFby a e, s))

(* unitialised delay, only works for ints for now, needs default / bottom *)
let pre (e: s int): s int = fby 0 e

(* "p -> q" in Lustre, first element of p followed by remainder of q *)
let (-->) (e1 e2: s 'a): s 'a =
  (fun s ->
    let (e1, s) = e1 s in
    let (e2, s) = e2 s in
    (XThen e1 e2, s))

let sofar (e: s bool): s bool =
  rec' (fun r -> e /\ fby true r)

let once (e: s bool): s bool =
  rec' (fun r -> e \/ fby false r)

let countsecutive (e: s bool): s int =
  rec' (fun r -> if_then_else e (fby 0 r +^ z1) (fby 0 r))

(* last-n, true for last n ticks *)
let last (n: nat) (e: s bool): s bool =
  countsecutive e <=^ z n
