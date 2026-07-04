(* TODO: README workaround 5 ("Clocked.map with anonymous lambdas").

   The lifter doesn't synthesize a core for an anonymous-function
   literal passed as the function arg of `Clocked.map`. The README
   suggests inlining the body (or hoisting the lambda to a named
   top-level let).

   This file pins the current behaviour:
     - `eg_map_named` (passing baseline): pass a named top-level helper.
     - `eg_map_lambda` (failing): pass `(fun p -> p.px)` directly.

   When anonymous-lambda map arguments start working, drop the
  `[@@expect_failure]` and remove workaround 5 from the TTCAN notes
  in `example/ttcan/readme.md`. *)
module Plugin.Test.Bug.MapLambda
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream
module PPL  = Pipit.Plugin.Lift

#set-options "--warn_error -242"

[@@derive_has_stream]
type point = { px: int; py: int; }

(* Local clocked-option type so we don't drag in TTCan modules. *)
type clk (a: eqtype) = option a

instance has_stream_clk (a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (clk a) = {
  ty_id       = `%clk :: (PSSB.ty_id #a);
  val_default = None;
}

let map (#a #b: eqtype) (fn: a -> b) (clck: clk a): clk b =
  match clck with
  | Some v -> Some (fn v)
  | None   -> None

(* Named top-level helper — works as the `fn` arg to `map`. *)
let take_px (p: point): int = p.px

(* Passing baseline: `map take_px c`. *)
let eg_map_named (c: stream (clk point)): stream (clk int) =
  map take_px c

(* Failing case: `map (fun p -> p.px) c` — anonymous lambda as the
   `fn` arg. Once this lifts, remove the comment-out below and add an
   `[@@expect_failure]` on the (auto-emitted) splice if it's still
   failing for a different reason. *)
//
// let eg_map_lambda (c: stream (clk point)): stream (clk int) =
//   map (fun p -> p.px) c
