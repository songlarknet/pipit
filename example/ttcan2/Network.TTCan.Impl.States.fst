(** State machines (mode, sync, master, ref-trigger-offset, ref-message, cycle-time)

   NONE of the streaming state machines in this module have been ported
   to the new pipeline yet. The known workarounds for the body-level
   issues are described in [example/ttcan2/README.md]; however a probe
   port of [cycle_time_capture] additionally surfaced two lifter-level
   bugs that need fixing in [Pipit.Source.Ast.Lower] before the rest of
   this module can be reduced to README workarounds:

     A. [type ntu = U64.t] (an alias chain that bottoms out at
        [FStar.UInt64.t]) is not normalised when comparing the body's
        inferred [shallow] type against the signature's declared
        [shallow] type. Even replacing [stream ntu] with
        [stream UInt64.t] in the return position leaves a
        "subtyping check failed" whose Expected/Got types are textually
        identical.

     B. Top-level non-stream let-bound constants such as
        [let msc_max: message_status_counter = S32R.s32r 7] hang the
        elaborator (typeclass resolution appears to loop) when later
        referenced inside a [#lang-pipit] streaming body. See
        [Network.TTCan.Impl.Errors.scheduling_error_1] for the
        companion TODO.
*)
module Network.TTCan.Impl.States

module Clocked = Network.TTCan.Prim.Clocked
module S32R    = Network.TTCan.Prim.S32R
module U64     = Network.TTCan.Prim.U64
module Util    = Network.TTCan.Impl.Util

open Network.TTCan.Types

(* ------------------------------------------------------------------ *
 * Probe port of [cycle_time_capture] - intentionally left red as a   *
 * reference for the alias-normalisation bug (A) noted above.         *
 *                                                                    *
 * Both the body and the signature elaborate to the textually         *
 * identical [shallow] type, yet the lifter rejects the binding with: *
 *                                                                    *
 *   Subtyping check failed                                           *
 *     Expected ... (Pipit.Prim.HasStream.shallow FStar.UInt64.t)     *
 *     Got      ... (Pipit.Prim.HasStream.shallow FStar.UInt64.t)     *
 *                                                                    *
 * Variants tried (all fail the same way):                            *
 *   - return type [stream ntu]                                       *
 *   - return type [stream U64.t]                                     *
 *   - return type [stream UInt64.t] (shown below)                    *
 *   - body's [U64.op_Subtraction] result cast to [<: ntu]            *
 *                                                                    *
 * ttcan2 is not part of the main build, so this stays as-is until    *
 * the lifter is taught to normalise type aliases.                    *
 * ------------------------------------------------------------------ *)
#lang-pipit
open Pipit.Source

(* Specialised wrappers around polymorphic Clocked/U64 helpers so the
   lifter sees a monomorphic call site - the poly form fails with a
   printer-identical [shallow ntu / shallow ntu] subtyping mismatch
   (the typeclass dictionaries differ in implicits the printer hides).
   See [example/ttcan2/README.md] section on Bug A. *)
let goe_ntu (dflt: ntu) (clck: Clocked.t ntu): ntu =
  Clocked.get_or_else dflt clck

let ntu_sub (a b: ntu): ntu = U64.op_Subtraction a b

(* -- Bisection probes for the Clocked.t-arg-in-let-rec bug -- *)

(* These pass: monomorphic helper called in [let rec] with no Clocked arg. *)
let probe_rec_sub_min (a: stream ntu): stream ntu =
  let rec x = ntu_sub a (0uL `fby` x) in x

let ntu_first (a _: ntu): ntu = a
let probe_rec_first (a: stream ntu): stream ntu =
  let rec x = ntu_first a (0uL `fby` x) in x

(* This also passes: stream of [option ntu] (Prims-defined parametric) as arg. *)
let ntu_or_else (dflt: ntu) (o: option ntu): ntu =
  match o with Some v -> v | None -> dflt
let probe_rec_option (c: stream (option ntu)): stream ntu =
  let rec x = ntu_or_else (0uL `fby` x) c in x

(* These FAIL with printer-identical [shallow ntu / shallow ntu]
   subtyping mismatch. The discriminator is: any [let rec] / [rec']
   body whose call passes a [stream (Clocked.t ntu)] arg. Arg order
   doesn't matter; [rec'] combinator instead of [let rec] doesn't help;
   removing or adding the explicit [has_stream_ntu] instance doesn't
   help. The fault lives in the lifter's typeclass-context plumbing
   for parametric [has_stream_t] instances under XMu binders.

   let ntu_first_clocked      (a: ntu) (_: Clocked.t ntu): ntu = a
   let ntu_first_clocked_swap (_: Clocked.t ntu) (a: ntu): ntu = a

   let probe_rec_first_clocked      (c: stream (Clocked.t ntu)): stream ntu =
     let rec x = ntu_first_clocked (0uL `fby` x) c in x
   let probe_rec_first_clocked_swap (c: stream (Clocked.t ntu)): stream ntu =
     let rec x = ntu_first_clocked_swap c (0uL `fby` x) in x
   let probe_rec_wrap               (c: stream (Clocked.t ntu)): stream ntu =
     let rec x = goe_ntu (0uL `fby` x) c in x
*)
let probe_recprime (c: stream (Clocked.t ntu)): stream ntu =
  rec' (fun x -> goe_ntu (0uL `fby` x) c)

let cycle_time_capture
  (local_time:         stream ntu)
  (reset_ck:           stream bool)
  (cycle_time_capture: stream (Clocked.t ntu))
    : stream ntu =
  let rec cycle_time_start =
    let dflt =
      if reset_ck
      then local_time
      else 0uL `fby` cycle_time_start
    in
    goe_ntu dflt cycle_time_capture
  in
  ntu_sub local_time cycle_time_start

let cycle_times
  (mode:       stream mode)
  (ref_mark:   stream (Clocked.t ntu))
  (local_time: stream ntu)
    : stream ntu =
  // Reset cycle_time=0 when leaving configure so Sync_Mode.TS1 holds.
  let cycle_time_reset =
    mode = Mode_Configure || pre (mode = Mode_Configure)
  in
  cycle_time_capture local_time cycle_time_reset ref_mark

(* Track the current mode based on mode commands seen so far. *)
let mode_states
  (mode_cmd: stream (Clocked.t mode))
    : stream mode =
  Clocked.current_or_else Mode_Configure mode_cmd
