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

type valtype' (a: Type) = v: valtype { ty_sem v == a }
type arithtype' (a: Type) = v: arithtype { ty_sem v == a }

class is_valtype (a: Type) = {
  is_valtype_get: valtype' a;
}

instance is_valtype_bool: is_valtype bool = {
  is_valtype_get = TBool;
}
instance is_valtype_int: is_valtype int = {
  is_valtype_get = TInt;
}
instance is_valtype_real: is_valtype R.real = {
  is_valtype_get = TReal;
}
instance is_valtype_pair {| is_valtype 'a |} {| is_valtype 'b |}: is_valtype ('a & 'b) = {
  is_valtype_get = TPair (is_valtype_get #'a) (is_valtype_get #'b);
}

class is_arithtype (a: Type) = {
  // is_arithtype_valtype: is_valtype a;
  is_arithtype_get: arithtype' a;
}
instance is_arithtype_int: is_arithtype int = {
  // is_arithtype_valtype = {| is_valtype int |};
  is_arithtype_get = TInt;
}
instance is_arithtype_real: is_arithtype R.real = {
  is_arithtype_get = TReal;
}

// type s  (a: valtype)  = S.s table a
type s (a: Type) = S.s' table a

type bools = s bool
type ints  = s int
type reals = s R.real

let run  (e: s 'a) : exp table [] 'a = S.run e

let run1 {| is_valtype 'a |} (f: s 'a -> s 'b) : exp table [is_valtype_get #'a ] 'b = S.run1 f
let run2 {| is_valtype 'a |} {| is_valtype 'b |} (f: s 'a -> s 'b -> s 'c) : exp table [is_valtype_get #'a; is_valtype_get #'b] 'c = S.run2 f

let pure {| is_valtype 'a |} (v: 'a): s 'a = S.pure #table #(is_valtype_get #'a) v

// LATER: explicit let' should not be necessary once we have CSE / sharing recovery
let let' {| is_valtype 'a |} {| is_valtype 'b |} (e: s 'a) (f: s 'a -> s 'b) = S.let' #table #(is_valtype_get #'a) #(is_valtype_get #'b) e f

let rec' {| is_valtype 'a |} (f: s 'a -> s 'a): s 'a = S.rec' #table #(is_valtype_get #'a) f

let check' {| is_valtype 'a |} (name: string) (e: bools) (f: s 'a): s 'a =
  S.check' #table #(is_valtype_get #'a) name e f

let fby {| is_valtype 'a |} (v: 'a) (e: s 'a): s 'a = S.fby #table #(is_valtype_get #'a) v e
let pre {| is_valtype 'a |} (e: s 'a): s 'a = S.pre #table #(is_valtype_get #'a) e
let (-->) {| is_valtype 'a |} (e1 e2: s 'a): s 'a = S.((-->) #table #(is_valtype_get #'a) e1 e2)


let tt: bools = pure true
let ff: bools = pure false

let z (i: int): ints = S.pure i
let z0 = z 0
let z1 = z 1

let zero {| is_arithtype 'a |}: s 'a = match is_arithtype_get #'a with
 | TInt  -> z0
 | TReal -> S.pure #table #(is_arithtype_get #'a) R.zero

(* Working with booleans *)
let (/\): bools -> bools -> bools = S.liftP2 (P'B P'B'And)
let (\/): bools -> bools -> bools = S.liftP2 (P'B P'B'Or)
let (=>): bools -> bools -> bools = S.liftP2 (P'B P'B'Implies)

let op_Negation: bools -> bools = S.liftP1 (P'B P'B'Not)
let (!^) = op_Negation
let not_ = op_Negation

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) {| is_valtype 'a |}: s 'a -> s 'a -> bools =
  S.liftP2 #table #(is_valtype_get #'a) #(is_valtype_get #'a) (P'V P'V'Eq (is_valtype_get #'a))
let (<>^) {| is_valtype 'a |}: s 'a -> s 'a -> bools =
  S.liftP2 #table #(is_valtype_get #'a) #(is_valtype_get #'a) (P'V P'V'Ne (is_valtype_get #'a))

let (+^) {| is_arithtype 'a |}: s 'a -> s 'a -> s 'a =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Add (is_arithtype_get #'a))
let (-^) {| is_arithtype 'a |}: s 'a -> s 'a -> s 'a =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Sub (is_arithtype_get #'a))
let (/^) {| is_arithtype 'a |}: s 'a -> s 'a -> s 'a =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Div (is_arithtype_get #'a))
let ( *^ ) {| is_arithtype 'a |}: s 'a -> s 'a -> s 'a =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Mul (is_arithtype_get #'a))

let (<=^) {| is_arithtype 'a |}: s 'a -> s 'a -> bools =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Le (is_arithtype_get #'a))
let (<^) {| is_arithtype 'a |}: s 'a -> s 'a -> bools =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Lt (is_arithtype_get #'a))
let (>=^) {| is_arithtype 'a |}: s 'a -> s 'a -> bools =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Ge (is_arithtype_get #'a))
let (>^) {| is_arithtype 'a |}: s 'a -> s 'a -> bools =
  S.liftP2 #table #(is_arithtype_get #'a) #(is_arithtype_get #'a) (P'A P'A'Gt (is_arithtype_get #'a))

let tup {| is_valtype 'a |} {| is_valtype 'b |}: s 'a -> s 'b -> s ('a & 'b) =
  S.liftP2 #table #(is_valtype_get #'a) #(is_valtype_get #'b) #(TPair (is_valtype_get #'a) (is_valtype_get #'b)) (P'T P'T'Pair (is_valtype_get #'a) (is_valtype_get #'b))

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
