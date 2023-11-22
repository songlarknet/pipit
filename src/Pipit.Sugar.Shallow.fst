(* Syntactic sugar for writing streaming programs, where all non-streaming
  operators are F* terms.
  This uses some splicing tactics and makes a few more assumptions about the
  front-end compared to the more minimalistic Vanilla front-end.
*)
module Pipit.Sugar.Shallow

module Table   = Pipit.Prim.Table
module Shallow = Pipit.Prim.Shallow

module PR  = PipitRuntime.Prim

module S = Pipit.Sugar.Base


module T = FStar.Tactics.V2

include Pipit.Sugar.Shallow.Base


let p'ftval (a: eqtype) {| has_stream a |}: Table.funty Shallow.shallow_type =
  Table.FTVal (shallow a)

let p'ftfun (a: eqtype) (r: Table.funty Shallow.shallow_type) {| has_stream a |}: Table.funty Shallow.shallow_type =
  shallow a `Table.FTFun` r


let p'prim1
  {| has_stream 'a |} {| has_stream 'r |}
  (prim_id:  option Shallow.ident)
  (prim_sem: 'a -> 'r): Shallow.prim =
  Shallow.mkPrim prim_id (p'ftfun 'a (p'ftval 'r)) prim_sem

let p'prim2
  {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'r |}
  (prim_id:  option Shallow.ident)
  (prim_sem: 'a -> 'b -> 'r): Shallow.prim =
  Shallow.mkPrim prim_id (p'ftfun 'a (p'ftfun 'b (p'ftval 'r))) prim_sem

let p'prim3
  {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'c |} {| has_stream 'r |}
  (prim_id:  option Shallow.ident)
  (prim_sem: 'a -> 'b -> 'c -> 'r): Shallow.prim =
  Shallow.mkPrim prim_id (p'ftfun 'a (p'ftfun 'b (p'ftfun 'c (p'ftval 'r)))) prim_sem



// let p'funty1 (a r: eqtype) {| has_stream a |} {| has_stream r |}: Table.funty Shallow.shallow_type =
//   shallow a `Table.FTFun` Table.FTVal (shallow r)
// let p'funty2 (a b r: eqtype) {| has_stream a |} {| has_stream b |} {| has_stream r |}: Table.funty Shallow.shallow_type =
//   shallow a `Table.FTFun` (shallow b `Table.FTFun` Table.FTVal (shallow r))
// let p'funty3 (a b c r: eqtype) {| has_stream a |} {| has_stream b |} {| has_stream c |} {| has_stream r |}: Table.funty Shallow.shallow_type =
//   shallow a `Table.FTFun` (shallow b `Table.FTFun` (shallow c `Table.FTFun` Table.FTVal (shallow r)))


// let liftP1
//   {| has_stream 'a |} {| has_stream 'r |}:
//   (S.prim Shallow.table (p'ftfun 'a (p'ftval 'r))) ->
//     s 'a ->
//     s 'r =
//   S.liftP1

// let liftP2
//   {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'r |}:
//   (S.prim Shallow.table (p'ftfun 'a (p'ftfun 'b (p'ftval 'r)))) ->
//     s 'a -> s 'b ->
//     s 'r =
//   S.liftP2

// let liftP3
//   {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'c |} {| has_stream 'r |}:
//   (S.prim Shallow.table (p'ftfun 'a (p'ftfun 'b (p'ftfun 'c (p'ftval 'r))))) ->
//     s 'a -> s 'b -> s 'c ->
//     s 'r =
//   S.liftP3


let tt: s bool = const true
let ff: s bool = const false

// let z (i: int): s int = const i
// let z0 = z 0
// let z1 = z 1

// let r (r: R.real): reals = const r
// let r0 = r 0.0R
// let r1 = r 1.0R

// let zero (#a: arithtype): s a = match a with
//  | TInt  -> z0
//  | TReal -> const R.zero

(* Working with booleans *)
let (/\): s bool -> s bool -> s bool = S.liftP2 PR.p'b'and
let (\/): s bool -> s bool -> s bool = S.liftP2 PR.p'b'or
let (=>): s bool -> s bool -> s bool = S.liftP2 PR.p'b'implies

// let op_Negation: bools -> bools = S.liftP1 (P'B P'B'Not)
// let (!^) = op_Negation
// let not_ = op_Negation

// (* Arithmetic operators, "^" suffix means "lifted" but unfortunately boolean operators such as /\^ do not parse *)
// let (=^) (#a: valtype): s a -> s a -> bools =
//   S.liftP2 (P'V P'V'Eq a)

// let (<>^) (#a: valtype): s a -> s a -> bools =
//   S.liftP2 (P'V P'V'Ne a)

// let (+^) (#a: arithtype): s a -> s a -> s a =
//   S.liftP2 (P'A P'A'Add a)
// let (-^) (#a: arithtype): s a -> s a -> s a =
//   S.liftP2 (P'A P'A'Sub a)
// let (/^) (#a: arithtype): s a -> s a -> s a =
//   S.liftP2 (P'A P'A'Div a)
// let ( *^ ) (#a: arithtype): s a -> s a -> s a =
//   S.liftP2 (P'A P'A'Mul a)

// let (<=^) (#a: arithtype): s a -> s a -> bools =
//   S.liftP2 (P'A P'A'Le a)
// let (<^) (#a: arithtype): s a -> s a -> bools =
//   S.liftP2 (P'A P'A'Lt a)
// let (>=^) (#a: arithtype): s a -> s a -> bools =
//   S.liftP2 (P'A P'A'Ge a)
// let (>^) (#a: arithtype): s a -> s a -> bools =
//   S.liftP2 (P'A P'A'Gt a)

// let ( %^ ): s TInt -> nonzero -> s TInt =
//   (fun a div -> S.liftP1 (P'I (P'I'ModConst div)) a)

// let tup (#a #b: valtype): s a -> s b -> s (TPair a b) =
//   S.liftP2 (P'T P'T'Pair a b)

// let fst (#a #b: valtype): s (TPair a b) -> s a =
//   S.liftP1 (P'T P'T'Fst a b)

// let snd (#a #b: valtype): s (TPair a b) -> s b =
//   S.liftP1 (P'T P'T'Snd a b)

// let negate (#a: arithtype) (r: s a) = zero -^ r

// (* if-then-else *)
// let ite (#a: valtype) : bools -> s a -> s a -> s a =
//   S.liftP3 (P'V P'V'IfThenElse a)

// let if_then_else (#a: valtype) = ite #a


// let sofar (e: bools): bools =
//   rec' (fun r -> e /\ fby true r)

// let once (e: bools): bools =
//   rec' (fun r -> e \/ fby false r)

// let countsecutive (e: bools): ints =
//   rec' (fun r -> if_then_else e (fby 0 r +^ z1) z0)

// (* last-n, true for last n ticks *)
// let last (n: nat) (e: bools): bools =
//   countsecutive e <=^ z n

// let abs (#a: arithtype) (r: s a): s a =
//   let^ r' = r in
//   if_then_else (r' >=^ zero) r' (zero -^ r')

// let sum (e: ints): ints =
//   rec' (fun r -> fby 0 r +^ e)

// let count (e: bools): ints =
//   sum (if_then_else e z1 z0)

