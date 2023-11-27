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
//     stream 'a ->
//     stream 'r =
//   S.liftP1

// let liftP2
//   {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'r |}:
//   (S.prim Shallow.table (p'ftfun 'a (p'ftfun 'b (p'ftval 'r)))) ->
//     stream 'a -> stream 'b ->
//     stream 'r =
//   S.liftP2

// let liftP3
//   {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'c |} {| has_stream 'r |}:
//   (S.prim Shallow.table (p'ftfun 'a (p'ftfun 'b (p'ftfun 'c (p'ftval 'r))))) ->
//     stream 'a -> stream 'b -> stream 'c ->
//     stream 'r =
//   S.liftP3

(* Helpers for inline anonymous primitives.
  In the future, when we implement CSE, it will be useful to have unique
  identifiers for each primitive. But, for now, it's convenient to declare
  anonymous primitives without needing to invent an identifier. *)

let lift1
  {| has_stream 'a |} {| has_stream 'r |}
  (f: Shallow.funty_sem (p'ftfun 'a (p'ftval 'r))):
    stream 'a ->
    stream 'r =
  S.liftP1 (p'prim1 None f)

let lift2
  {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'r |}
  (f: Shallow.funty_sem (p'ftfun 'a (p'ftfun 'b (p'ftval 'r)))):
    stream 'a ->
    stream 'b ->
    stream 'r =
  S.liftP2 (p'prim2 None f)

let lift3
  {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'c |} {| has_stream 'r |}
  (f: Shallow.funty_sem (p'ftfun 'a (p'ftfun 'b (p'ftfun 'c (p'ftval 'r))))):
    stream 'a ->
    stream 'b ->
    stream 'c ->
    stream 'r =
  S.liftP3 (p'prim3 None f)


let tt: stream bool = const true
let ff: stream bool = const false

(* Working with booleans.
  Unfortunately, there aren't many suitable operators for boolean or: none of
  (||), (||^) or (\/^) are allowed. We could use raw (\/) but that gets
  annoying when we want propositional or in properties, and it's not
  totally consistent as `not` doesn't work...
 *)
let (/\):  stream bool -> stream bool -> stream bool =
  S.liftP2 (p'prim2 (Some [`%PR.p'b'and]) PR.p'b'and)
let (\/):  stream bool -> stream bool -> stream bool =
  S.liftP2 (p'prim2 (Some [`%PR.p'b'or]) PR.p'b'or)
let (==>): stream bool -> stream bool -> stream bool =
  S.liftP2 (p'prim2 (Some [`%PR.p'b'implies]) PR.p'b'implies)

let notb: stream bool -> stream bool =
  S.liftP1 (p'prim1 (Some [`%PR.p'b'not]) PR.p'b'not)

unfold let (~) = notb

let (=) (#a: eqtype) {| has_stream a |}: stream a -> stream a -> stream bool =
  S.liftP2 (p'prim2 #a #a (Some [`%(=)]) (fun x y -> x = y))

let (<>) (#a: eqtype) {| has_stream a |}: stream a -> stream a -> stream bool =
  S.liftP2 (p'prim2 #a #a (Some [`%(<>)]) (fun x y -> x <> y))

let tup (#a #b: eqtype) {| has_stream a |} {| has_stream b |}: stream a -> stream b -> stream (a & b) #_ =
  lift2 (fun x y -> (x, y))

// why does this not work with named prim?
// let tup2 (#a #b: eqtype) {| has_stream a |} {| has_stream b |}: stream a -> stream b -> stream (a & b) #_ =
  // S.liftP2 (p'prim2 #a #b #(a&b) (Some [`%Mktuple2]) (fun x y -> (x, y)))

let fst (#a #b: eqtype) {| has_stream a |} {| has_stream b |}: stream (a & b) #_ -> stream a =
  lift1 (fun (xy: (a & b)) -> fst xy)

let snd (#a #b: eqtype) {| has_stream a |} {| has_stream b |}: stream (a & b) #_ -> stream b =
  lift1 (fun (xy: (a & b)) -> snd xy)

(* if-then-else *)
let select (#a: eqtype) {| has_stream a |} : stream bool -> stream a -> stream a -> stream a =
  S.liftP3 (p'prim3 #bool #a #a (Some [`%PR.p'select]) PR.p'select)

let if_then_else (#a: eqtype) {| has_stream a |} = select #a

let sofar (e: stream bool): stream bool =
  rec' (fun r -> e /\ fby true r)

let once (e: stream bool): stream bool =
  rec' (fun r -> e \/ fby false r)
