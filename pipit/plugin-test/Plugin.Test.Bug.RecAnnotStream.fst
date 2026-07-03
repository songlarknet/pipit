(* TODO: README workaround 13 ("rec' lambda parameter with explicit
   stream type annotation").

   In `Network.TTCan.Impl.Controller.trigger_tx`, the following shape
   failed under #lang-pipit:

     rec' (fun (tx_app_msc_upd: stream (Clocked.t can_buffer_id &
                                        Clocked.t bool)) -> ...)

   with "Identifier not found: stream". The workaround documented in
   the TTCan README was to drop the annotation and let F* infer the
   parameter type.

   This file pins the actual trigger experimentally. Contrary to
   the README's original wording, the trigger is JUST the explicit
   `stream T` annotation on the rec' lambda parameter — `let open M
   in` in the body is incidental: a fully-qualified body in an
   annotated rec' still fails identically.

   Hypothesis: the `#lang-pipit` preprocessor strips the `stream`
   keyword from top-level binder annotations, but does not descend
   into lambdas inside `rec' (fun (x: stream T) -> ...)`. F* then
   sees the raw `stream` identifier (which only the preprocessor
   resolves) and reports "Identifier not found: stream".

   Fixed: `pre_term`'s `Abs` case now applies `mode_of_pattern` to
   each lambda parameter, stripping `stream` from type annotations
   just like `pre_letbind` does for top-level let bindings. The
   parameter type annotation is processed before F* sees it.

   This file pins the boundary:
     - `eg_rec_unannot` (baseline) — no annotation on the rec'
       lambda param. Works.
     - `eg_rec_annot` — now PASSES after the fix.

   Remove this TODO comment and workaround 13 from
   `example/ttcan2/README.md` once the fix ships. *)
module Plugin.Test.Bug.RecAnnotStream
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream
module U64  = FStar.UInt64

#set-options "--warn_error -242"

instance has_stream_U64: PSSB.has_stream U64.t = {
  ty_id       = [`%U64.t];
  val_default = 0uL;
}

(* Baseline: rec' lambda parameter UN-annotated. Works regardless of
   whether the body uses fully-qualified ops or `let open U64 in`. *)
let eg_rec_unannot (x: stream U64.t): stream U64.t =
  rec' (fun acc ->
    U64.add_mod (0uL `fby` acc) x)

let eg_rec_unannot_let_open (x: stream U64.t): stream U64.t =
  rec' (fun acc ->
    let open U64 in
    (0uL `fby` acc) +%^ x)

(* Failing case: rec' lambda parameter explicitly annotated with
   `stream U64.t`. Reproduces

     Error 72: Identifier not found: stream

   pointing at the annotation. The `let open U64 in` form is not
   involved — a fully-qualified body fails identically when the
   parameter is annotated.

   Commented out so the rest of the module compiles. *)
let eg_rec_annot (x: stream U64.t): stream U64.t =
  rec' (fun (acc: stream U64.t) ->
    U64.add_mod (0uL `fby` acc) x)

let eg_inner_let_stream_annot (x: stream U64.t): stream U64.t =
  rec' (fun (acc: stream U64.t) ->
    let count': stream U64.t = U64.add_mod (0uL `fby` acc) x in
    count')
