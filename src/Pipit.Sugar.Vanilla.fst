(* Syntactic sugar for writing nice-ish stream programs.
   This module provides a type constructor for streams `s 'a` and combinators
   for combining them together.
   There are `run`, `run1` and `run2` functions for converting stream programs
   to core expressions, but these should really be hidden...
*)
module Pipit.Sugar.Vanilla

open Pipit.Prim.Vanilla

module S = Pipit.Sugar.Base

module R = FStar.Real

let table = table

type valtype = valtype
type arithtype = arithtype

type stream (a: valtype)  = S.stream table a

type bools = stream TBool
type ints  = stream TInt
type reals = stream TReal

let const (#a: valtype) (v: table.ty_sem a): stream a = S.const #table #a v

(* Applicative / monadic syntactic sugar:
  The syntactic sugar for let^ is made for monads, but it seems to work OK for
  our (applicative) case by changing the type slightly. The type of the bound
  variable becomes a wrapped `stream 'a` rather than a raw `'a`. However, the `and^`
  and pattern matching don't work, as they expect a raw `'a`.
*)
let (let^) (f:stream 'a) (g: stream 'a -> stream 'b) =
    S.let' #table #'a #'b f g

// let (and^) (f:stream 'a) (g: stream 'b): stream (TPair 'a 'b) =
//   S.liftP2 (P'T P'T'Pair 'a 'b) f g

let rec' (f: stream 'a -> stream 'a): stream 'a = S.rec' #table #'a f

let letrec' (f: stream 'a -> stream 'a) (g: stream 'a -> stream 'b): stream 'b =
  let^ a = rec' f in g a

(* letrec with multiple bindings can require duplicating work.
  this duplicate work is troublesome for proofs because the transition system will
  have multiple state variables that mean the same thing, but that aren't trivially
  equivalent when looking at the state on its own.
  in practice, it is often possible to rearrange an expression to avoid duplication.
  how do we characterise expressions where such rearrangement is possible? *)
let letrec2 (#a #b #k: valtype)
  (mka: stream a -> stream b -> stream a)
  (mkb: stream a -> stream b -> stream b)
  (kont: stream a -> stream b -> stream k):
    stream k =
  (* let rec
       a = (rec a. mka a (rec b. mkb a b))
       b = (rec b. mkb a b)
     in kont a b
  *)
  let recb a = rec' (fun b -> mkb a b) in
  let^ a = (rec' (fun a -> mka a (recb a))) in
  let^ b = recb a in
  kont a b

let check (name: string) (e: bools): bools =
  S.check #table e

let check_that (#a: valtype) (e: stream a) (p: stream a -> bools): stream a =
  let^ scrut = e in
  check "" (p scrut);^
  scrut

let fby (#a: valtype) (v: table.ty_sem a) (e: stream a): stream a = S.fby #table #a v e

let pre (e: stream 'a): stream 'a = S.pre #table #'a e

let (->^) (e1 e2: stream 'a): stream 'a =
  S.liftP3 (P'V P'V'IfThenElse 'a)
    (fby #TBool true (const false))
    e1 e2

let tt: bools = const true
let ff: bools = const false

let z (i: int): ints = const i
let z0 = z 0
let z1 = z 1

let r (r: R.real): reals = const r
let r0 = r 0.0R
let r1 = r 1.0R

let zero (#a: arithtype): stream a = match a with
 | TInt  -> z0
 | TReal -> const R.zero

(* Working with booleans *)
let (/\): bools -> bools -> bools = S.liftP2 (P'B P'B'And)
let (\/): bools -> bools -> bools = S.liftP2 (P'B P'B'Or)
let (=>): bools -> bools -> bools = S.liftP2 (P'B P'B'Implies)

let op_Negation: bools -> bools = S.liftP1 (P'B P'B'Not)
let (!^) = op_Negation
let not_ = op_Negation

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) (#a: valtype): stream a -> stream a -> bools =
  S.liftP2 (P'V P'V'Eq a)

let (<>^) (#a: valtype): stream a -> stream a -> bools =
  S.liftP2 (P'V P'V'Ne a)

let (+^) (#a: arithtype): stream a -> stream a -> stream a =
  S.liftP2 (P'A P'A'Add a)
let (-^) (#a: arithtype): stream a -> stream a -> stream a =
  S.liftP2 (P'A P'A'Sub a)
let (/^) (#a: arithtype): stream a -> stream a -> stream a =
  S.liftP2 (P'A P'A'Div a)
let ( *^ ) (#a: arithtype): stream a -> stream a -> stream a =
  S.liftP2 (P'A P'A'Mul a)

let (<=^) (#a: arithtype): stream a -> stream a -> bools =
  S.liftP2 (P'A P'A'Le a)
let (<^) (#a: arithtype): stream a -> stream a -> bools =
  S.liftP2 (P'A P'A'Lt a)
let (>=^) (#a: arithtype): stream a -> stream a -> bools =
  S.liftP2 (P'A P'A'Ge a)
let (>^) (#a: arithtype): stream a -> stream a -> bools =
  S.liftP2 (P'A P'A'Gt a)

let ( %^ ): stream TInt -> nonzero -> stream TInt =
  (fun a div -> S.liftP1 (P'I (P'I'ModConst div)) a)

let tup (#a #b: valtype): stream a -> stream b -> stream (TPair a b) =
  S.liftP2 (P'T P'T'Pair a b)

let fst (#a #b: valtype): stream (TPair a b) -> stream a =
  S.liftP1 (P'T P'T'Fst a b)

let snd (#a #b: valtype): stream (TPair a b) -> stream b =
  S.liftP1 (P'T P'T'Snd a b)

let negate (#a: arithtype) (r: stream a) = zero -^ r

(* if-then-else *)
let ite (#a: valtype) : bools -> stream a -> stream a -> stream a =
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

let abs (#a: arithtype) (r: stream a): stream a =
  let^ r' = r in
  if_then_else (r' >=^ zero) r' (zero -^ r')

let sum (e: ints): ints =
  rec' (fun r -> fby 0 r +^ e)

let count (e: bools): ints =
  sum (if_then_else e z1 z0)
