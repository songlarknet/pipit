(* TODO: README workaround 4 ("pre #T expr — explicit type-arg uses").
   STATUS (2026-06-08). No reproducer remains.

   The TTCan2 `pre` helper

     let pre (#a: eqtype) {| PSSB.has_stream a |} (v: stream a): stream a =
       PSSB.val_default `fby` v

   was historically claimed to fail under the lifter when called with
   an explicit `#T` type-arg annotation. As of 2026-06-08, both
   `pre s` (implicit) and `pre #int s` lift cleanly, including for
   `option a` (where the type-arg is itself parameterised by another
   `has_stream`).

   This file pins the current behaviour as a regression probe. If a
   future change re-breaks the explicit form, comment out the
   `eg_pre_explicit_*` cases below and re-add the workaround to
   `example/ttcan2/README.md`. *)
module Plugin.Test.Bug.PreExplicitType
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

#set-options "--warn_error -242"

instance has_stream_option (a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (option a) = {
  ty_id       = `%option :: (PSSB.ty_id #a);
  val_default = None;
}

let pre (#a: eqtype) {| PSSB.has_stream a |} (v: stream a): stream a =
  PSSB.val_default `fby` v

(* Baseline: implicit-type-arg call. *)
let eg_pre_implicit_T (s: stream int): stream int =
  let p = pre s in
  p + 1

(* Probe: explicit `#int` type-arg call. *)
let eg_pre_explicit_T (s: stream int): stream int =
  let p = pre #int s in
  p + 1

(* Probe: explicit type-arg with a parameterised `has_stream` instance. *)
let eg_pre_explicit_option (s: stream (option int)): stream (option int) =
  pre #(option int) s
