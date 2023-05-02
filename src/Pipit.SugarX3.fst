(* Streaming effect, based on fstar/examples/layeredeffects/Locals.Effect *)
module Pipit.SugarX3

open Pipit.Exp.Base

module C = Pipit.Context

module Pure = FStar.Monotonic.Pure

let stream = Pipit.Exp.Base.exp []

type state = {
  fresh: nat;
}

// -> GTot Type0?
let strm_pre = state -> Type0
let strm_post (a: Type) = a -> state -> Type0
let strm_wp0 (a: Type) = strm_post a -> strm_pre

unfold
let strm_wp_monotonic (a: Type) (wp: strm_wp0 a) =
  forall (p q: strm_post a).
    (forall x m. p x m ==> q x m) ==>
    (forall   m. wp p m ==> wp q m)

let strm_wp (a: Type) = wp: strm_wp0 a { strm_wp_monotonic a wp }

type repr (a: Type) (wp: strm_wp a) =
  s: state -> PURE (a & state) (Pure.as_pure_wp (fun p -> wp (fun r s' -> p (r, s')) s))

unfold
let return_wp (a: Type) (x: a) (post: strm_post a) = post x

let return (a: Type) (x: a): repr a (return_wp a x) =
  fun s -> (x, s)

unfold
let bind_wp (a b: Type)
  (wp1: strm_wp a) (wp2: a -> strm_wp b)
  (post: strm_post b)
  (s: state) =
 wp1 (fun a s' -> wp2 a post s') s

let bind (a b: Type)
  (wp_f: strm_wp a)
  (wp_g: a -> strm_wp b)
  (f: repr a wp_f)
  (g: (x: a -> repr b (wp_g x))):
    repr b (bind_wp a b wp_f wp_g) =
  fun s ->
    let (x, s') = f s in
    g x s'

let subcomp (a: Type)
  (wp_f wp_g: strm_wp a)
  (f: repr a wp_f):
    Pure (repr a wp_g)
  (requires forall p s. wp_g p s ==> wp_f p s)
  (ensures fun _ -> True) = f

unfold
let if_then_else (a: Type)
  (wp_f wp_g: strm_wp a)
  (f: repr a wp_f)
  (g: repr a wp_g)
  (p: bool): Type =
  repr a (fun post s -> (p ==> wp_f post s) /\ ((~ p) ==> wp_g post s))

total reifiable reflectable
effect {
  STREAM (a: Type) (_: strm_wp a)
  with { repr; return; bind; subcomp; if_then_else }
}

unfold
let lift_pure_wp (#a: Type) (wp: pure_wp a): strm_wp a =
  Pure.elim_pure_wp_monotonicity wp;
  fun p s -> wp (fun x -> p x s)

let lift_pure_stream (a: Type) (wp: pure_wp a) (f: unit -> PURE a wp):
  repr a (lift_pure_wp wp) =
 Pure.elim_pure_wp_monotonicity wp;
 fun s -> f (), s

sub_effect PURE ~> STREAM = lift_pure_stream

effect StreamH (a: Type) (pre: strm_pre) (post: strm_post a) = STREAM a (fun post' s -> pre s /\ (forall (x: a) (s': state). post x s' ==> post' x s'))

effect Stream (a: Type) = StreamH a (requires (fun s -> True)) (ensures (fun a s -> True))

let fresh (t: Type): Stream (C.var t) =
  STREAM?.reflect (fun s ->
    let var = s.fresh in
    C.Var var, { fresh = var + 1 })


let let'
  (e: stream 'a)
  (f: stream 'a -> Stream (stream 'b)):
    Stream (stream 'b) =
  let xvar = fresh 'a in
  let evar: stream 'a = XVar xvar in
  let e' = f evar in
  XLet 'a e (close1 e' xvar)

let rec'
  (f: stream 'a -> Stream (stream 'a)):
    Stream (stream 'a) =
  let xvar = fresh 'a in
  let evar: stream 'a = XVar xvar in
  let e' = f evar in
  XMu (close1 e' xvar)

let check'
  (name: string)
  (e: stream bool)
  (f: stream 'a):
    Stream (stream 'a) =
  XCheck name e f

let pure (a: 'a): stream 'a =
  XVal a

let (<$>)
  (f: ('a -> 'b))
  (a: stream 'a):
      stream 'b =
  XApp (XVal f) a

let (<*>)
  (f: stream ('a -> 'b))
  (a: stream 'a):
      stream 'b =
  XApp f a

let liftA1
  (f: ('a -> 'b))
  (a: stream 'a):
      stream 'b =
  f <$> a

let liftA2
  (f: ('a -> 'b -> 'c))
  (a: stream 'a)
  (b: stream 'b):
      stream 'c =
  f <$> a <*> b

let liftA3
  (f: ('a -> 'b -> 'c -> 'd))
  (a: stream 'a)
  (b: stream 'b)
  (c: stream 'c):
      stream 'd =
  f <$> a <*> b <*> c

let tt: stream bool = pure true
let ff: stream bool = pure true

let z (i: int): stream int = XVal i
let z0 = z 0
let z1 = z 1

(* Working with booleans *)
let (/\) = liftA2 (fun x y -> if x then y else false)
let (\/) = liftA2 (fun x y -> if x then true else y)
let (=>) = liftA2 (fun x y -> if x then y else true)

let not = liftA1 not
let op_Negation = liftA1 not
let (!^) = liftA1 not

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) (#t: eqtype) (a b: stream t): stream bool = liftA2 (fun x y -> x = y) a b

let (<>^) (#t: eqtype) (a b: stream t): stream bool = !^ (a =^ b)

let (+^) = liftA2 (+)
let (-^) = liftA2 (fun x y -> x - y)

let (<=^) = liftA2 (<=)
let (>=^) = liftA2 (>=)
let (<^) = liftA2 (<)
let (>^) = liftA2 (>)

let negate = liftA1 (fun x -> -x)

(* if-then-else *)
let ite = liftA3 (fun x y z -> if x then y else z)

(* unitialised delay *)
let fby (a: 'a) (e: stream 'a): stream 'a = XFby a e

(* "p -> q" in Lustre, first element of p followed by remainder of q *)
let (-->) (e1 e2: stream 'a): stream 'a = XThen e1 e2

let sofar (e: stream bool): Stream (stream bool) =
  rec' (fun r -> e /\ fby true r)

let once (e: stream bool): Stream (stream bool) =
  rec' (fun r -> e \/ fby false r)

let countsecutive (e: stream bool): Stream (stream int) =
  rec' (fun r -> ite e (fby 0 r +^ z1) (fby 0 r))

(* last-n, true for last n ticks *)
let last (n: nat) (e: stream bool): Stream (stream bool) =
  countsecutive e <=^ z n
