(* TODO: README workaround 6 ("Record projections as first-class
   function values").
   STATUS (2026-06-08). No reproducer remains.

   Passing a record projector (e.g. `Mkpoint?.px`) as a first-class
   function to a higher-order helper like `Clocked.map` was
   historically claimed to fail in the lifter. As of 2026-06-08, both
   `map (fun p -> p.px) c` and `map Mkpoint?.px c` lift cleanly when
   the local `map` is a plain `eqtype -> eqtype` polymorphic helper.

   The §5 case (anonymous-lambda function argument) remains live —
   see `Plugin.Test.Bug.MapLambda` for that probe.

   This file pins the current behaviour as a regression probe. If a
   future change re-breaks the projector form, comment out the
   `eg_map_proj_*` cases below and re-add the workaround to
   `example/ttcan2/README.md`. *)
module Plugin.Test.Bug.MapProjector
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

#set-options "--warn_error -242"

[@@derive_has_stream]
type point = { px: int; py: int; }

[@@derive_has_stream]
type ref_t = { cycle_index: int; sof: bool; }

type clk (a: eqtype) = option a

instance has_stream_clk (a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (clk a) = {
  ty_id       = `%clk :: (PSSB.ty_id #a);
  val_default = None;
}

let map (#a #b: eqtype) (fn: a -> b) (clck: clk a): clk b =
  match clck with
  | Some v -> Some (fn v)
  | None   -> None

(* Baseline: named projection helper. *)
let take_px (p: point): int = p.px

let eg_map_named (c: stream (clk point)): stream (clk int) =
  map take_px c

(* Probe: first-class projector `Mkpoint?.px`. *)
let eg_map_proj_point (c: stream (clk point)): stream (clk int) =
  map Mkpoint?.px c

(* Probe: first-class projector on the record shape from the original
   TTCan2 workaround. *)
let eg_map_proj_ref_t (c: stream (clk ref_t)): stream (clk int) =
  map Mkref_t?.cycle_index c
