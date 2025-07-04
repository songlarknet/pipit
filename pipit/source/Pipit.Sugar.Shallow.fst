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
  (prim_id:  option string)
  (prim_sem: 'a -> 'r): Shallow.prim =
  Shallow.mkPrim prim_id (p'ftfun 'a (p'ftval 'r)) prim_sem

let p'prim2
  {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'r |}
  (prim_id:  option string)
  (prim_sem: 'a -> 'b -> 'r): Shallow.prim =
  Shallow.mkPrim prim_id (p'ftfun 'a (p'ftfun 'b (p'ftval 'r))) prim_sem

let p'prim3
  {| has_stream 'a |} {| has_stream 'b |} {| has_stream 'c |} {| has_stream 'r |}
  (prim_id:  option string)
  (prim_sem: 'a -> 'b -> 'c -> 'r): Shallow.prim =
  Shallow.mkPrim prim_id (p'ftfun 'a (p'ftfun 'b (p'ftfun 'c (p'ftval 'r)))) prim_sem

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
  S.liftP2 (p'prim2 (Some (`%PR.p'b'and)) PR.p'b'and)
let (\/):  stream bool -> stream bool -> stream bool =
  S.liftP2 (p'prim2 (Some (`%PR.p'b'or)) PR.p'b'or)
let (==>): stream bool -> stream bool -> stream bool =
  S.liftP2 (p'prim2 (Some (`%PR.p'b'implies)) PR.p'b'implies)

let notb: stream bool -> stream bool =
  S.liftP1 (p'prim1 (Some (`%PR.p'b'not)) PR.p'b'not)

unfold let (~) = notb

let (=) (#a: eqtype) {| has_stream a |}: stream a -> stream a -> stream bool =
  S.liftP2 (p'prim2 #a #a (Some (`%(=))) (fun x y -> x = y))

let (<>) (#a: eqtype) {| has_stream a |}: stream a -> stream a -> stream bool =
  S.liftP2 (p'prim2 #a #a (Some (`%(<>))) (fun x y -> x <> y))

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
  S.liftP3 (p'prim3 #bool #a #a (Some (`%PR.p'select)) PR.p'select)

let if_then_else (#a: eqtype) {| has_stream a |} = select #a

let sofar (e: stream bool): stream bool =
  rec' (fun r -> e /\ fby true r)

let once (e: stream bool): stream bool =
  rec' (fun r -> e \/ fby false r)

(* Ideas for improving syntax:

  rename fby to fby', implement fby with type (s a -> s a -> s a)
    fby (XVal v) e' = XFby v e'
    fby e e' = if (XFby true false) then e else XFby bottom e'

  implicit coercions from a -> s a
    how badly will type inference suffer?

  select/if-then-else syntax maybe `select [x ->: e1; y ->: e2]`
    `select [cond1 ->: e1; cond2 ->: e2] generates assertion (cond1 \/ cond2)`

  named tuple syntax?
    `Tuple.t ["x",  U64.t; "y", Clocked.t U64.t]`
    `x ^. "x"`
*)



module Check = Pipit.Sugar.Check
module T = Pipit.Tactics
module Lift = Pipit.Sugar.Shallow.Tactics.Lift

(** Propose a lemma instantiation with the given pattern.

  It's currently difficult to instantiate lemmas explicitly, because they
  live in prop, while our properties are restricted to booleans.
  Previously I had an axiom for this, which converted the proposition to
  a boolean, but it's not clear how sound that is.

  The version here doesn't require any axioms. To instantiate a lemma, we
  need to define an opaque pattern function that takes the lemma arguments and
  returns a unit. We then define the lemma with an [SMTPat p] so it triggers on
  seeing the pattern p. We can then put the pattern itself into the program.

  The implementation introduces a check that `p = ()`, because otherwise the
  let-bound pattern can be removed as dead code.

*)
[@@Lift.lifted; Lift.of_source(`%Lift.lemma_pattern)]
let lemma_pattern: stream unit -> stream unit =
  let e = Check.exp_of_stream1 (fun pat -> check "" (pat = const ())) in
  assert (Check.system_induct_k 0 e) by (T.norm_full []);
  Check.stream_of_checked1 e
