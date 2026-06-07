(* Regression test for README workaround 3 ("cross-module non-stream
   helpers called from #lang-pipit").

   The original symptom: a plain F* helper such as

     let opt_get_or_else (dflt: int) (clck: option int): int =
       match clck with Some v -> v | None -> dflt

   defined OUTSIDE a `#lang-pipit` module and WITHOUT a
   [@@source_mode ...] attribute, called from a `#lang-pipit` body
   with a `let`-bound *stream* local in the [dflt] position, was
   reported to fail with `Variable XYZ not found` at the static lower
   pass.

   This probe puts the helper in a non-`#lang-pipit` module
   (`Plugin.Test.Bug.CrossModHelper.Helpers`) and calls it from a
   `#lang-pipit` body with a `let`-bound stream argument. Today
   (2026-06-08) it passes — including a [rec'] variant that wraps the
   stream local in a feedback loop, mirroring the
   `Network.TTCan.Impl.States.cycle_time_capture` usage that
   originally motivated workaround 3.

   When this stops passing, workaround 3 has regressed; when it keeps
   passing, the README's claim about [Clocked.get_or_else]-style
   helpers (now [Network.TTCan.Prim.Clocked] is itself `#lang-pipit`)
   has weakened to "MSC64.* / BV64I.* are speculative — no known
   reproducer". *)
module Plugin.Test.Bug.CrossModHelper
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream
module H    = Plugin.Test.Bug.CrossModHelper.Helpers

instance has_stream_option (#a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (option a) = {
  ty_id       = `%option :: (PSSB.ty_id #a);
  val_default = None;
}

(* Simple call site: stream-bound [dflt] passed to a plain
   non-`#lang-pipit` helper. *)
let probe_helper_with_stream_dflt (clck: stream (option int)): stream int =
  let dflt: stream int = 0 in
  H.opt_get_or_else dflt clck

(* [rec'] variant: the stream local is the recursive feedback, which
   was the shape that bit in `cycle_time_capture`. *)
let probe_helper_in_rec (clck: stream (option int)): stream int =
  rec' (fun acc ->
    let dflt: stream int = 0 `fby` acc in
    H.opt_get_or_else dflt clck)

(* Two-argument helper where the stream local flows through a
   different slot. *)
let probe_helper_two_streams (a b: stream int): stream int =
  let mid: stream int = a + b in
  H.add_then_clamp mid 100
