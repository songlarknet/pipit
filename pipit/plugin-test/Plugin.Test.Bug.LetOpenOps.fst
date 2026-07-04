(* TODO: README workaround 7 ("let open M in ... with operators").
   STATUS (2026-06-08). No reproducer remains.

   Bringing operator symbols into scope with `let open M in ...` was
   historically claimed to break the lifter, with the workaround being
   to replace each `+^`/`-^`/`*^`/`<^`/etc. with its fully qualified
   form (`U64.op_Plus` / `U64.add` / `U64.add_mod` / ...). As of
   2026-06-08, all of the `FStar.UInt64` arithmetic and comparison
   operators lift cleanly inside a `let open U64 in ...` block.

   This file pins the current behaviour as a regression probe. If a
  future change re-breaks operator resolution under `let open`,
  comment out the `eg_ops_let_open_*` cases below and re-add the
  workaround to the TTCAN notes in `example/ttcan/readme.md`. *)
module Plugin.Test.Bug.LetOpenOps
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream
module U64  = FStar.UInt64

#set-options "--warn_error -242"

instance has_stream_U64: PSSB.has_stream U64.t = {
  ty_id       = [`%U64.t];
  val_default = 0uL;
}

(* Baseline: explicit qualified-function form (modular variants so we
   don't need bounds-checking lemmas). *)
let eg_ops_explicit (x: stream U64.t) (y: stream U64.t) (z: stream U64.t): stream U64.t =
  U64.sub_mod (U64.add_mod x y) z

(* Probe: arithmetic operators under `let open`. *)
let eg_ops_let_open_arith (x: stream U64.t) (y: stream U64.t) (z: stream U64.t): stream U64.t =
  let open U64 in x +%^ y -%^ z

(* Probe: multiplication under `let open` (modular form). *)
let eg_ops_let_open_mul (x: stream U64.t) (y: stream U64.t): stream U64.t =
  let open U64 in x *%^ y

(* Probe: comparison operator under `let open`. *)
let eg_ops_let_open_lt (x: stream U64.t) (y: stream U64.t): stream bool =
  let open U64 in x <^ y
