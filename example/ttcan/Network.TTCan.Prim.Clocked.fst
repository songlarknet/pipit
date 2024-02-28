(* Helpers for encoding clocked streams *)
module Network.TTCan.Prim.Clocked

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

open Pipit.Sugar.Shallow.Tactics.Lift

module REPR    = FStar.UInt64
module UInt    = FStar.UInt

type t (a: eqtype) = option a

instance has_stream_t (a: eqtype) {| Sugar.has_stream a |}: Sugar.has_stream (t a) = {
  ty_id = `%t :: (Sugar.ty_id #a);
  val_default = None;
}

let get_clock (#a: eqtype) (v: t a): bool = Some? v
let get_value (#a: eqtype) {| Sugar.has_stream a |} (v: t a): a =
  match v with
  | Some v -> v
  | None -> Sugar.val_default

(* Pattern matching on a single clocked value *)
let fold (#a #b: eqtype)
  (zero: b)
  (kons: a -> b)
  (clck: t a)
       : b =
  match clck with
  | Some v -> kons v
  | None -> zero

(* Pattern matching on a stream of clocked values *)
// let fold_stream1 (#a #b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |}
//   (zero: Sugar.stream b)
//   (kons: Sugar.stream a -> Sugar.stream b)
//   (clck: Sugar.stream (t a))
//        : Sugar.stream b =
//   Sugar.if_then_else (clck.clock) (kons (get_value clck)) zero

(* Safely extracting a value *)
let get_or_else (#a: eqtype) (dflt: a) (clck: t a): a =
  fold dflt (fun v -> v) clck


let map (#a #b: eqtype) (fn: a -> b) (clck: t a): t b = FStar.Option.mapTot fn clck

(* Aggregation over a stream of clocked values *)
// noeq
// type stream_fold_args (a b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |} = {
//   initial: b;
//   update:  Sugar.stream a -> Sugar.stream b -> Sugar.stream b;
//   clocked: Sugar.stream (t a);
//   reset:   Sugar.stream bool;
// }

// let stream_fold (#a #b: eqtype) {| Sugar.has_stream a |} {| Sugar.has_stream b |} (args: stream_fold_args a b)
//        : Sugar.stream b =
//   let open Sugar in
//   rec' (fun acc ->
//     let^ prev = if_then_else args.reset (const args.initial) (args.initial `fby` acc) in
//     fold prev (fun v -> args.update v prev) args.clocked
//   )

let current_or_else (#a: eqtype) {| Sugar.has_stream a |} (dflt: a) (clck: stream (t a)): stream a =
  rec' (fun acc ->
    get_or_else (dflt `fby` acc) clck)

%splice[current_or_else_core] (autolift_binds [`%current_or_else])

let or_else (#a: eqtype) (u v: t a): t a =
  match u with
  | Some _ -> u
  | None   -> v
