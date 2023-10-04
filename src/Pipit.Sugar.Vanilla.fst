(* Syntactic sugar for writing nice-ish stream programs.
   This module provides a type constructor for streams `s 'a` and combinators
   for combining them together.
   There are `run`, `run1` and `run2` functions for converting stream programs
   to core expressions, but these should really be hidden...
*)
module Pipit.Sugar.Vanilla

open Pipit.Prim.Vanilla

open Pipit.Exp.Base
open Pipit.Exp.Binding

module C  = Pipit.Context.Base

module S = Pipit.Sugar.Base

module R = FStar.Real

let table = table

type valtype = valtype
type arithtype = arithtype

type s (a: valtype)  = S.s table a

type bools = s TBool
type ints  = s TInt
type reals = s TReal

let pure (#a: valtype) (v: table.ty_sem a): s a = S.pure #table #a v

// LATER: explicit let' should not be necessary once we have CSE / sharing recovery
let let' (e: s 'a) (f: s 'a -> s 'b) = S.let' #table #'a #'b e f

let rec' (f: s 'a -> s 'a): s 'a = S.rec' #table #'a f

let letrec' (f: s 'a -> s 'a) (g: s 'a -> s 'b): s 'b = let' (rec' f) g

(* letrec with multiple bindings can require duplicating work.
  this duplicate work is troublesome for proofs because the transition system will
  have multiple state variables that mean the same thing, but that aren't trivially
  equivalent when looking at the state on its own.
  in practice, it is often possible to rearrange an expression to avoid duplication.
  how do we characterise expressions where such rearrangement is possible? *)
let letrec2 (#a #b #k: valtype)
  (mka: s a -> s b -> s a)
  (mkb: s a -> s b -> s b)
  (kont: s a -> s b -> s k):
    s k =
  (* let rec
       a = (rec a. mka a (rec b. mkb a b))
       b = (rec b. mkb a b)
     in kont a b
  *)
  letrec' (fun a -> mka a (rec' (fun b -> mkb a b)))
                             (fun a ->
  letrec' (fun b -> mkb a b) (fun b ->
    kont a b))

let check' (name: string) (e: bools) (f: s 'a): s 'a =
  S.check' #table #'a e f

let check (name: string) (e: bools): bools =
  S.check #table e

let check_that (#a: valtype) (e: s a) (p: s a -> bools): s a =
  let' e (fun scrut -> S.check' (p scrut) scrut)

let fby (#a: valtype) (v: table.ty_sem a) (e: s a): s a = S.fby #table #a v e

let pre (e: s 'a): s 'a = S.pre #table #'a e

let (-->) (e1 e2: s 'a): s 'a =
  S.liftP3 (P'V P'V'IfThenElse 'a)
    (fby #TBool true (pure false))
    e1 e2

let tt: bools = pure true
let ff: bools = pure false

let z (i: int): ints = S.pure i
let z0 = z 0
let z1 = z 1

let r (r: R.real): reals = S.pure r
let r0 = r 0.0R
let r1 = r 1.0R

let zero (#a: arithtype): s a = match a with
 | TInt  -> z0
 | TReal -> S.pure R.zero

(* Working with booleans *)
let (/\): bools -> bools -> bools = S.liftP2 (P'B P'B'And)
let (\/): bools -> bools -> bools = S.liftP2 (P'B P'B'Or)
let (=>): bools -> bools -> bools = S.liftP2 (P'B P'B'Implies)

let op_Negation: bools -> bools = S.liftP1 (P'B P'B'Not)
let (!^) = op_Negation
let not_ = op_Negation

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) (#a: valtype): s a -> s a -> bools =
  S.liftP2 (P'V P'V'Eq a)

let (<>^) (#a: valtype): s a -> s a -> bools =
  S.liftP2 (P'V P'V'Ne a)

let (+^) (#a: arithtype): s a -> s a -> s a =
  S.liftP2 (P'A P'A'Add a)
let (-^) (#a: arithtype): s a -> s a -> s a =
  S.liftP2 (P'A P'A'Sub a)
let (/^) (#a: arithtype): s a -> s a -> s a =
  S.liftP2 (P'A P'A'Div a)
let ( *^ ) (#a: arithtype): s a -> s a -> s a =
  S.liftP2 (P'A P'A'Mul a)

let (<=^) (#a: arithtype): s a -> s a -> bools =
  S.liftP2 (P'A P'A'Le a)
let (<^) (#a: arithtype): s a -> s a -> bools =
  S.liftP2 (P'A P'A'Lt a)
let (>=^) (#a: arithtype): s a -> s a -> bools =
  S.liftP2 (P'A P'A'Ge a)
let (>^) (#a: arithtype): s a -> s a -> bools =
  S.liftP2 (P'A P'A'Gt a)

let tup (#a #b: valtype): s a -> s b -> s (TPair a b) =
  S.liftP2 (P'T P'T'Pair a b)

let fst (#a #b: valtype): s (TPair a b) -> s a =
  S.liftP1 (P'T P'T'Fst a b)

let snd (#a #b: valtype): s (TPair a b) -> s b =
  S.liftP1 (P'T P'T'Snd a b)

let negate (#a: arithtype) (r: s a) = zero -^ r

(* if-then-else *)
let ite (#a: valtype) : bools -> s a -> s a -> s a =
  S.liftP3 (P'V P'V'IfThenElse a)

let if_then_else (#a: valtype) = ite #a


let sofar (e: bools): bools =
  rec' (fun r -> e /\ fby true r)

let once (e: bools): bools =
  rec' (fun r -> e \/ fby false r)

let countsecutive (e: bools): ints =
  rec' (fun r -> if_then_else e (fby 0 r +^ z1) z0)

(* last-n, true for last n ticks *)
let last (n: nat) (e: bools): bools =
  countsecutive e <=^ z n

let abs (#a: arithtype) (r: s a): s a =
  let' r (fun r' ->
    if_then_else (r' >=^ zero) r' (zero -^ r'))
