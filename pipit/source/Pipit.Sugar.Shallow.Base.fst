(* Syntactic sugar for writing streaming programs, where all non-streaming
  operators are F* terms.
  This uses some splicing tactics and makes a few more assumptions about the
  front-end compared to the more minimalistic Vanilla front-end.
*)
module Pipit.Sugar.Shallow.Base

module Table   = Pipit.Prim.Table
module Shallow = Pipit.Prim.Shallow

module PR  = PipitRuntime.Prim

module S = Pipit.Sugar.Base
module L = FStar.List.Tot

class has_stream (a: eqtype) = {
  ty_id:       Shallow.ident;
  val_default: a;
}

let shallow (a: eqtype) {| strm: has_stream a |} : Shallow.shallow_type = {
  ty_id       = strm.ty_id;
  ty_sem      = a;
  val_default = strm.val_default;
}

instance has_stream_bool: has_stream bool = {
  ty_id       = [`%Prims.bool];
  val_default = false;
}

instance has_stream_unit: has_stream unit = {
  ty_id       = [`%Prims.unit];
  val_default = ();
}

instance has_stream_tup2 {| a: has_stream 'a |} {| b: has_stream 'b |}: has_stream ('a & 'b) = {
  ty_id       = L.(`%Pervasives.tuple2 :: a.ty_id @ b.ty_id);
  val_default = (a.val_default, b.val_default);
}

type stream (a: eqtype) {| has_stream a |} = S.stream Shallow.table (shallow a)

let const {| has_stream 'a |} (v: 'a): stream 'a = S.const v

(* Applicative / monadic syntactic sugar:
  The syntactic sugar for let^ is made for monads, but it seems to work OK for
  our (applicative) case by changing the type slightly. The type of the bound
  variable becomes a wrapped `stream 'a` rather than a raw `'a`. However, the `and^`
  and pattern matching don't work, as they expect a raw `'a`.
*)
let (let^) {| has_stream 'a |}  {| has_stream 'b |} (f:stream 'a) (g: stream 'a -> stream 'b) =
    S.let' f g

// let (and^) (f:stream 'a) (g: stream 'b): stream (TPair 'a 'b) =
//   S.liftP2 (P'T P'T'Pair 'a 'b) f g

let rec' {| has_stream 'a |} (f: stream 'a -> stream 'a): stream 'a = S.rec' f

let check (name: string) (e: stream bool): stream unit =
  S.check e

let check_that {| has_stream 'a |} (e: stream 'a) (p: stream 'a -> stream bool): stream 'a =
  let^ scrut = e in
  check "" (p scrut);^
  scrut


let fby {| has_stream 'a |} (v: 'a) (e: stream 'a): stream 'a = S.fby v e

let pre {| has_stream 'a |} (e: stream 'a): stream 'a = S.pre e

private
let p'select (a: eqtype) {| has_stream a |}: Shallow.prim =
  Shallow.mkPrim (Some (`%PR.p'select)) (shallow bool `Table.FTFun` (shallow a `Table.FTFun` (shallow a `Table.FTFun` (Table.FTVal (shallow a))))) PR.p'select

(* x -> y in Lustre means "x" at the first step, and then "y" at subsequent steps.
  we also bind this operator as (->^) for lifted arrow
 *)
let subsequently {| has_stream 'a |} (e1 e2: stream 'a): stream 'a =
  let^ init_flag = true `fby` (const false) in
  S.liftP3 (p'select 'a) init_flag e1 e2

let (->^) {| has_stream 'a |} (e1 e2: stream 'a): stream 'a = e1 `subsequently` e2
