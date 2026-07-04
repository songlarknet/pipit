(* Self-contained debug twin of the splice-driven extraction pipeline in
  [example/Example.Simple.Extract]. Defines its own source binding
  ([count_when]) via the manual [lift_ast_tac1] entry point (i.e. the
  non-[#lang-pipit] equivalent, as in [Plugin.Test.Source.SimpleCheckPort]),
  then hand-expands the four bindings the [Pipit.Plugin.Extract.extract]
  splice would emit ([count_when_state], [__extractable_count_when],
  [count_when_system], [count_when_reset], [count_when_step]) and wires
  each one through the [tac_specialize_strict_*_debug] variants instead
  of the production [tac_specialize_strict_*]. The debug tactics print
  the goal before and after each [Tac.norm] pass via [Tac.print] /
  [Tac.term_to_string] but never fail on surviving forbidden FQNs.

  To compare against the strict (failing) tactic on any binding, flip
  the attribute from [..._debug] back to the non-debug variant.

  Lives in plugin-test rather than example/ because it's not part of
  the production extract pipeline and shouldn't be a target of
  [make example-extract]. *)
module Plugin.Test.Simple.Extract.Debug

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
open Pipit.Plugin.Interface
open Pipit.Source

module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.PulseExtract
module SL  = Pipit.Exp.SimplifyLet
module PT  = Pipit.Tactics
module Tac = FStar.Tactics

(* ---- 1. Source binding ----
  Lifts to [count_when_core] (carries the [core_of_source "count_when"]
  attribute). Same body as [Example.Simple.Check.count_when]. *)

[@@source_mode (ModeFun Stream true Stream)]
let count_when (p: bool): int =
  rec' (fun count -> (0 `fby` count) + (if p then 1 else 0))
%splice[] (PPL.lift_ast_tac1 "count_when")

(* ---- 2. Extraction parameters ---- *)

(* The "namespaces" list the strict tactic unfolds through. Mirrors the
  list the splice computes (source-defining module + target module — here
  both are this same module). *)
noextract
let ns_list: list string =
  ["Plugin.Test.Simple.Extract.Debug"]

(* The "extras" passed to the pulse strict tactic — local helpers that
  must (a) be unfolded and (b) not survive normalization. *)
noextract
let pulse_extras: list string =
  ["Plugin.Test.Simple.Extract.Debug.count_when_state";
   "Plugin.Test.Simple.Extract.Debug.count_when_system"]

(* ---- 3. state ---- *)
[@@(Tac.postprocess_with (XL.tac_specialize_strict_pure_debug ns_list []))]
let count_when_state: Type0 =
  XX.state_of_exp (SL.simplify count_when_core)

(* ---- 4. extractable proof ---- *)
[@@noextract_to "krml"]
let __extractable_count_when
  : squash (XX.extractable (SL.simplify count_when_core))
=
  FStar.Tactics.Effect.synth_by_tactic (fun () ->
    PT.norm_full ns_list;
    FStar.Tactics.V2.exact (`()))

(* ---- 5. system ---- *)
[@@(Tac.postprocess_with (XL.tac_specialize_strict_pure_debug ns_list ["Plugin.Test.Simple.Extract.Debug.count_when_state"]))]
noextract
inline_for_extraction
let count_when_system
  : XX.esystem (bool & unit) count_when_state int
=
  (fun (_: squash (XX.extractable (SL.simplify count_when_core))) ->
     XX.exec_of_exp (SL.simplify count_when_core))
  __extractable_count_when

(* ---- 6. reset ---- *)
[@@(Tac.postprocess_with (XL.tac_specialize_strict_pulse_debug ns_list pulse_extras))]
let count_when_reset =
  XL.mk_reset (XL.mk_init count_when_system)

(* ---- 7. step ---- *)
[@@(Tac.postprocess_with (XL.tac_specialize_strict_pulse_debug ns_list pulse_extras))]
let count_when_step (p: bool) =
  XL.mk_step (fun i st -> XL.mk_step_pure count_when_system i st) (p, ())
