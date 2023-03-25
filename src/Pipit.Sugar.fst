(* Meagre syntactic sugar for constructing expressions.
  Want a HOAS-to-de-bruijn transform. *)
module Pipit.Sugar

open Pipit.Exp.Base

(* Literals *)
let tt = XVal 1
let ff = XVal 0

let z (i: int) = XVal i
let z0 = z 0
let z1 = z 1

(* Variable helpers *)
let x0 = XVar 0
let x1 = XVar 1
let x2 = XVar 2

(* Working with booleans *)
let (/\) = XPrim2 AndB
let (\/) = XPrim2 OrB
let (=>) = XPrim2 ImpliesB

(* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
let (=^) = XPrim2 EqZ
let (+^) = XPrim2 AddZ
let (-^) = XPrim2 SubZ
let (<=^) = XPrim2 LeZ
let (>=^) (a b: exp)  = b <=^ a
let (<^) (a b: exp) = (a +^ z1) <=^ b
let (>^) (a b: exp) = (b +^ z1) <=^ a

let (!) (e1: exp) = e1 =^ ff
let (<>^) (a b: exp) = !(a =^ b)

let negate (e1: exp) = z0 -^ e1

(* if-then-else *)
let ite (ep et ef: exp) = XIte ep et ef

(* unitialised delay *)
let pre (e: exp) = XPre e

(* "p -> q" in Lustre, first element of p followed by remainder of q *)
let (-->) (e1 e2: exp) = XThen e1 e2

(* unsafe binding forms / variable management *)
let mu' (e: exp): exp = XMu e
let let' (e1 e2: exp): exp = XLet e1 e2
let lift' (e: exp) = Pipit.Exp.Subst.lift e 0

(* modal logic operators: G (always in the past) *)
let sofar (e: exp): exp =
  mu' (lift' e /\ (tt --> pre x0))

(* F (at least once in the past) *)
let once (e: exp): exp =
  mu' (lift' e \/ (ff --> pre x0))

(* count of consecutively true *)
let countsecutive (e: exp): exp =
  mu' (ite (lift' e) (pre x0 +^ z1) z0)

(* last-n, true for last n ticks *)
let last (n: nat) (e: exp): exp =
  z n <=^ countsecutive e
