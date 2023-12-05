(* Helpers for encoding clocked streams *)
module Network.TTCan.Prim.Clocked

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module REPR    = FStar.UInt64
module UInt    = FStar.UInt

type t (a: eqtype) = {
  value: a;
  clock: bool;
}

instance has_stream_t (a: eqtype) {| Sugar.has_stream a |}: Sugar.has_stream (t a) = {
  ty_id = `%t :: (Sugar.ty_id #a);
  val_default = { value = Sugar.val_default; clock = Sugar.val_default; };
}

let some' (#a: eqtype) (value: a): t a = { value; clock = true; }
let none' (#a: eqtype) {| Sugar.has_stream a |}: t a = { value = Sugar.val_default; clock = false; }




%splice[some] (SugarTac.lift_prim "some" (`some'))

// lift_prim tac does not support consts yet
let none (#a: eqtype) {| Sugar.has_stream a |}: Sugar.stream (t a) #(has_stream_t a) =
  Sugar.const (none' #a)

%splice[get_clock] (SugarTac.lift_prim "get_clock" (`(fun (#a: eqtype) (r: t a) -> r.clock)))

%splice[get_value] (SugarTac.lift_prim "get_value" (`(fun (#a: eqtype) (r: t a) -> r.value)))

(* Pattern matching on a single clocked value *)
let fold' (#a #b: eqtype)
  (zero: b)
  (kons: a -> b)
  (clck: t a)
       : b =
  if clck.clock then kons clck.value else zero

(* Pattern matching on a stream of clocked values *)
let fold (#a #b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |}
  (zero: Sugar.stream b)
  (kons: Sugar.stream a -> Sugar.stream b)
  (clck: Sugar.stream (t a))
       : Sugar.stream b =
  Sugar.if_then_else (get_clock clck) (kons (get_value clck)) zero

(* Safely extracting a value *)
let get_or_else (#a: eqtype) {| Sugar.has_stream a |}
  (dflt: Sugar.stream a)
  (clck: Sugar.stream (t a))
       : Sugar.stream a =
  fold dflt (fun v -> v) clck


let map (#a #b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |}
  (fn: Sugar.stream a -> Sugar.stream b)
  (clck: Sugar.stream (t a))
       : Sugar.stream (t b) =
  Sugar.if_then_else (get_clock clck) (some (fn (get_value clck))) none

(* Aggregation over a stream of clocked values *)
noeq
type stream_fold_args (a b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |} = {
  initial: b;
  update:  Sugar.stream a -> Sugar.stream b -> Sugar.stream b;
  clocked: Sugar.stream (t a);
  reset:   Sugar.stream bool;
}

let stream_fold (#a #b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |} (args: stream_fold_args a b)
       : Sugar.stream b =
  let open Sugar in
  rec' (fun acc ->
    let^ prev = if_then_else args.reset (const args.initial) (args.initial `fby` acc) in
    fold prev (fun v -> args.update v prev) args.clocked
  )

let current_or_else (#a: eqtype) {| Sugar.has_stream a |} (dflt: a) (clck: Sugar.stream (t a)): Sugar.stream a =
  let open Sugar in
  rec' (fun acc ->
    get_or_else (dflt `fby` acc) clck)