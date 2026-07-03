(* TODO: README workaround 11 ("[@@proof_induct1] on bindings with
   static prefix arguments").

   The preprocessor synthesises a `__check_<id>` declaration of the
   form
     let __check_<id> =
       assert (induct1 (system_of_exp __core_<id>)) by (norm_full []);
       ()
   This presumes `__core_<id>` is of type `exp ...`. When the source
   binding has Static parameters BEFORE its stream parameters (e.g.
   `(max: int) (inc: stream bool)`), `__core_<id>` ends up at type
   `max: int -> exp ...`, so the spliced check fails to elaborate
   with "Expected expression of type `exp ...`, got expression
   `<id>_core` of type `max: int -> exp ...`".

   This file pins the current behaviour:
     - `count_when_no_static` (baseline) — same logic without the
       static `max` arg; `[@@proof_induct1]` discharges normally.
     - `count_when` (commented out) — TTCAN's actual shape with a
       leading `(max: int)`; `[@@proof_induct1]` cannot elaborate.

   Uncomment the second block to reproduce. When fixed, drop the
   comment-out and remove workaround 11 from
   `example/ttcan2/README.md`. *)
module Plugin.Test.Bug.ProofInductStatic
#lang-pipit

open Pipit.Source

#set-options "--warn_error -242"

(* Baseline: no static prefix. `[@@proof_induct1]` discharges; the
   `check` is a tautology held by the saturating recursion. *)
[@@proof_induct1]
let count_when_no_static (inc: stream bool): stream int =
  let rec count =
    let count' = (0 `fby` count) + (if inc then 1 else 0) in
    if count' > 100 then 100 else count'
  in
  check (0 <= count && count <= 100);
  count

(* Failing case: identical body but the bound `100` is lifted to a
   Static `max: int` parameter. The auto-emitted `__check_count_when`
   splice tries to evaluate
     assert (induct1 (system_of_exp __core_count_when))
   but `__core_count_when` has type `max: int -> exp ...`, so the
   elaboration fails inside the splice itself.

   Fixed: `mk_check_induct1_decl` now extracts the static prefix
   binders and emits:
     let __check_count_when (max: int) =
       assert (induct1 (system_of_exp (count_when_core max))) by ...

   Both the baseline (no static arg) and the static-prefix case now
   verify. Remove this TODO comment and workaround 11 from
   example/ttcan2/README.md once TriggerTimely is re-enabled. *)

[@@proof_induct1]
let count_when (max: int { max >= 0 }) (inc: stream bool): stream int =
  let rec count =
    let count' = (0 `fby` count) + (if inc then 1 else 0) in
    if count' > max then max else count'
  in
  check (0 <= count && count <= max);
  count

(* Mixed ordering: stream arg before static arg.  The lifter still hoists
   `max` as the outermost binder of `count_when_mixed_core`, so
   `__check_count_when_mixed` must apply `max` even though it follows
   `inc` in source order. *) 
[@@proof_induct1]
let count_when_mixed (inc: stream bool) (max: int { max >= 0 }): stream int =
  let rec count =
    let count' = (0 `fby` count) + (if inc then 1 else 0) in
    if count' > max then max else count'
  in
  check (0 <= count && count <= max);
  count
