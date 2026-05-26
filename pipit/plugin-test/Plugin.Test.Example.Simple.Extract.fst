module Plugin.Test.Example.Simple.Extract

(* Hand-written port of [example/Simple.Extract.fst] to the new plugin
  source pipeline. We extract a step function for [count_when] from
  [Plugin.Test.Example.Simple.Check].

  TODO: most of the body below is mechanical and we will eventually
  auto-generate it from a [%splice[...] (derive_extract "count_when")]
  splice. *)

module Simple    = Plugin.Test.Example.Simple.Check

module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.Pulse
module SL  = Pipit.Exp.SimplifyLet
module PT  = Pipit.Tactics
module Tac = FStar.Tactics

(* Namespace prefix passed to the extraction tactics. Any name beginning
  with this prefix is unfolded during normalization. [noextract] because
  this is a tactic-time helper that should not appear in the generated C. *)
noextract
unfold
let ns: list string = ["Plugin.Test.Example.Simple"]

(* The lifted core expression for [Simple.count_when]. We re-bind it so the
  rest of the file does not have to mention the internal [__core_*] name.

  We post-process with [SimplifyLet.simplify] to inline trivial
  [let x = bvar in ...] aliases that the lifter introduces when applying
  primitives like [fby_core]. Without this, the inner [let x = count in
  0 fby x] inside the [rec'] body causes [Pipit.Exp.Causality.causal] to
  conservatively reject the program. [simplify] is intended to be
  semantics-preserving; the bigstep preservation proof is future work.

  [@@postprocess_with norm_full ns] together with [noextract] means F* sees
  through to the simplified core during downstream normalization, while
  KaRaMeL skips the binding entirely. *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure ns))]
noextract
let expr = SL.simplify Simple.__core_count_when

(* State type for the system. The postprocess pass inlines
  [state_of_exp expr] to a concrete type so it lands in the generated C. *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure ns))]
type state = XX.state_of_exp expr

type result = int

(* Build the transition system from the expression. We annotate the input
  row as [bool & unit] to match a single [stream bool] argument.

  The [extractable] precondition is discharged by [norm_full] rather than
  [assert_norm] because [__core_*] bindings are tagged with the irreducible
  [core_lifted] attribute; [norm_full] adds [delta_attr [core_lifted; ...]]
  so the lifted body actually unfolds. *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure ns))]
noextract
inline_for_extraction
let system: XX.esystem (bool & unit) state result =
  let _: squash (XX.extractable expr) = _ by (PT.norm_full ns; Tac.trivial ()) in
  XX.exec_of_exp expr

(* Pulse-level [reset] and [step]. *)
[@@(Tac.postprocess_with (XL.tac_extract ns))]
let reset = XL.mk_reset (XL.mk_init system)

[@@(Tac.postprocess_with (XL.tac_extract ns))]
let step (inp: bool) =
  XL.mk_step (fun i st -> XL.mk_step_pure system (i, ()) st) inp
