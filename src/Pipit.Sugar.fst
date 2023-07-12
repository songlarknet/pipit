(* Syntactic sugar for writing nice-ish stream programs.
   This module provides a type constructor for streams `s 'a` and combinators
   for combining them together.
   There are `run`, `run1` and `run2` functions for converting stream programs
   to core expressions, but these should really be hidden...
*)
module Pipit.Sugar

open Pipit.Prim.Vanilla

open Pipit.Exp.Base
open Pipit.Exp.Binding

module C  = Pipit.Context.Base

module S = Pipit.Sugar.Base

module R = FStar.Real

type s (t: valtype) = S.s table t
type bools = s TBool
type ints = s TInt

let run (#a: valtype) (e: s a) : val_exp table [] a = S.run e
let run1 (#a #b: valtype) (f: s a -> s b) : val_exp table [a] b = S.run1 f
let run2 (#a #b #c: valtype) (f: s a -> s b -> s c) : val_exp table [a; b] c = S.run2 f

let pure (#t: valtype) (v: table.ty_sem t): s t = S.pure v

// LATER: explicit let' should not be necessary once we have CSE / sharing recovery
let let' (#a #b: valtype) (e: s a) (f: s a -> s b) = S.let' e f

let rec' (#a: valtype) (f: s a -> s a): s a = S.rec' f

let check' (#a: valtype) (name: string) (e: bools) (f: s a): s a =
  S.check' name e f

let fby (#a: valtype) (v: ty_sem a) (e: s a): s a = S.fby v e
let pre (#a: valtype) (e: s a): s a = S.pre e
let (-->) (#a: valtype) (e1 e2: s a): s a = S.(e1 --> e2)


let tt: bools = pure true
let ff: bools = pure false

let z (i: int): ints = S.pure i
let z0 = z 0
let z1 = z 1

let zero (#t: arithtype): s t = match t with
 | TInt  -> z0
 | TReal -> pure R.zero

(* Working with booleans *)
let (/\): bools -> bools -> bools = S.liftP2 (P'B P'B'And)
let (\/): bools -> bools -> bools = S.liftP2 (P'B P'B'Or)
let (=>): bools -> bools -> bools = S.liftP2 (P'B P'B'Implies)

let op_Negation: bools -> bools = S.liftP1 (P'B P'B'Not)
let (!^) = op_Negation
let not_ = op_Negation

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) (#t: valtype): s t -> s t -> bools = S.liftP2 (P'V P'V'Eq t)
let (<>^) (#t: valtype): s t -> s t -> bools = S.liftP2 (P'V P'V'Ne t)

let (+^) (#t: arithtype): s t -> s t -> s t = S.liftP2 (P'A P'A'Add t)
let (-^) (#t: arithtype): s t -> s t -> s t = S.liftP2 (P'A P'A'Sub t)
let (/^) (#t: arithtype): s t -> s t -> s t = S.liftP2 (P'A P'A'Div t)
let ( *^ ) (#t: arithtype): s t -> s t -> s t = S.liftP2 (P'A P'A'Mul t)

let (<=^) (#t: arithtype): s t -> s t -> bools = S.liftP2 (P'A P'A'Le t)
let (<^) (#t: arithtype): s t -> s t -> bools = S.liftP2 (P'A P'A'Lt t)
let (>=^) (#t: arithtype): s t -> s t -> bools = S.liftP2 (P'A P'A'Ge t)
let (>^) (#t: arithtype): s t -> s t -> bools = S.liftP2 (P'A P'A'Gt t)

let tup (#a #b: valtype): s a -> s b -> s (TPair a b) = S.liftP2 (P'T P'T'Pair a b)
let fst (#a #b: valtype): s (TPair a b) -> s a = S.liftP1 (P'T P'T'Fst a b)
let snd (#a #b: valtype): s (TPair a b) -> s b = S.liftP1 (P'T P'T'Snd a b)

// let negate = 0

(* if-then-else *)
let ite (#t: valtype): bools -> s t -> s t -> s t = S.liftP3 (P'V P'V'IfThenElse t)
let if_then_else (#t: valtype) = ite #t


let sofar (e: bools): bools =
  S.rec' (fun r -> e /\ S.fby true r)

let once (e: bools): bools =
  S.rec' (fun r -> e \/ S.fby false r)

let countsecutive (e: bools): ints =
  S.rec' (fun r -> if_then_else e (fby 0 r +^ z1) (fby 0 r))

(* last-n, true for last n ticks *)
let last (n: nat) (e: bools): bools =
  countsecutive e <=^ z n

let abs (#t: arithtype) (r: s t): s t =
  let' r (fun r' ->
    if_then_else (r' >=^ zero) r' (zero -^ r'))
