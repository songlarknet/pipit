(* Simple Pulse-based integration for mutable state extraction. *)
module Pipit.Exec.Pulse
#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

module EE = Pipit.Exec.Exp
module Tac = FStar.Tactics
module PTB = Pipit.Tactics.Base
module PEB = Pipit.Exp.Base
module L = FStar.List.Tot
module S = FStar.String

let tac_extract_full_strong_core (namespaces: list string) (local_delta: list string) =
  let base_delta = [
    "Pipit.Exec.Pulse.mk_step_pure";
    "Pipit.Context.Row.index";
    "FStar.Pervasives.coerce_eq"
  ] in
  Tac.norm [
    nbe;
    primops;
    iota;
    zeta;
    delta_namespace ("Pipit" :: "FStar.Pervasives" :: namespaces);
    delta_only (local_delta @ base_delta);
    delta_qualifier ["inline_for_extraction"];
    delta_attr [`%Pipit.Tactics.norm_attr]
  ];
  Tac.norm [
    zeta_full;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only local_delta
  ]

let tac_normalize_pure (namespaces: list string) () =
  Pipit.Tactics.norm_full namespaces;
  Tac.trefl ()

(*
let tac_extract (namespaces: list string) () =
  let opts ns = [
    nbe;
    primops;
    iota;
    zeta_full;
    delta_namespace ("Pipit" :: "FStar.Pervasives" :: ns);
    delta_qualifier ["inline_for_extraction"];
    delta_attr [`%Pipit.Tactics.norm_attr]
  ] in
  Tac.norm (opts namespaces);
  Tac.trefl ()
*)

noextract inline_for_extraction
let mk_init (#input #state #output: Type)
  (t: EE.esystem input state output)
  : state
=
  match t with
  | { init = init_v; step = _ } -> init_v

noextract inline_for_extraction
let mk_step_pure (#input #state #output: Type)
  (t: EE.esystem input state output)
  (inp: input)
  (st: state)
  : (state & output)
=
  match t with
  | { init = _; step = step_f } -> step_f inp st

(* The [requires]/[ensures] clauses on the Pulse [fn]s below desugar to
  literal slprop lambdas ([fun _ -> R.pts_to st e] for the unit-returning
  case, [fun out -> R.pts_to st (fst ...) ** pure (out == snd ...)] for
  the result-returning case). F* SMT-encodes those lambdas verbatim and
  emits warning 249 ("Losing precision when encoding a function
  literal") at every call site of the resulting [stt unit pre post]
  computation type — i.e. every spliced [_reset]/[_step] in a
  consumer module like [Example.Simple.Extract].

  Hoisting the postcondition body into a named [unfold] helper does
  not silence the warning (the encoder still unfolds inline). Marking
  the helper plain (non-[unfold]) breaks the Pulse body proof, since
  Pulse can no longer see the underlying [R.pts_to] inside
  [helper ...]. The mismatch is a known limitation of the SMT
  encoder, not a soundness issue — see upstream Pulse's
  [ParallelIncrement.fst] which suppresses the same warning around its
  own [fn] definitions.

  Consumer modules that splice Pulse extracts and want to silence the
  warning at the splice site should push [--warn_error -249] (or
  [--warn -249] to also hide the message) around the splice. The
  [Pipit.Plugin.Extract] splice currently leaves the choice to the
  consumer; the production [Example.*.Extract] files do so. *)

noextract inline_for_extraction
fn mk_reset (#state: eqtype)
  (init_v: state)
  (st: ref state)
  requires R.pts_to st 'n
  ensures R.pts_to st init_v
{
  st := init_v
}

noextract inline_for_extraction
fn mk_step (#input #result #state: eqtype)
  (step_f: input -> state -> (state & result))
  (inp: input)
  (st: ref state)
  requires R.pts_to st 'n
  returns out: result
  ensures R.pts_to st (fst (step_f inp 'n))
  ensures pure (out == snd (step_f inp 'n))
{
  let s = !st;
  let next = step_f inp s;
  let s' = fst next;
  let out = snd next;
  st := s';
  out
}

noextract inline_for_extraction
fn mk_reset_sys (#input #state #output: eqtype)
  (t: EE.esystem input state output)
  (st: ref state)
  requires R.pts_to st 'n
  ensures R.pts_to st (mk_init t)
{
  st := mk_init t
}

noextract inline_for_extraction
fn mk_step_sys (#input #state #output: eqtype)
  (t: EE.esystem input state output)
  (inp: input)
  (st: ref state)
  requires R.pts_to st 'n
  returns out: output
  ensures R.pts_to st (fst (mk_step_pure t inp 'n))
  ensures pure (out == snd (mk_step_pure t inp 'n))
{
  let s = !st;
  let next = mk_step_pure t inp s;
  let s' = fst next;
  let out = snd next;
  st := s';
  out
}



(* Strong-enough normalization for extracting both single- and multi-input
  Pulse systems. The deltas are written for the common case where the
  result of [mk_step]/[mk_reset] is normalized down to plain Pulse with
  no surviving [Pipit_Context_Row_index] / [coerce_eq__any_any] calls.

  Two subtle requirements (both load-bearing for the multi-input case):

  * [zeta_full] instead of plain [zeta]. The recursive case of
    [Pipit.Context.Row.index] introduces a let-binding [ts = ...] via an
    [iota]-match on the row list; plain [zeta] does not propagate that
    binding deeply enough for the recursive [index] call to fire, so
    the recursion stalls. With [zeta_full] the substitution happens and
    the recursion fully unfolds.

  * [FStar.Pervasives.coerce_eq] in [delta_only]. The recursive case of
    [Row.index] wraps its result in [coerce_eq] to reconcile two
    index-list views; without unfolding the coercion the wrapper
    survives in C as an unimplemented [coerce_eq__any_any] call. *)
let tac_extract (namespaces: list string) () =
  Tac.norm [
    zeta_full;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only [
      `%mk_init;
      `%mk_step_pure;
      `%mk_reset;
      `%mk_step;
      `%mk_reset_sys;
      `%mk_step_sys;
      `%Pipit.Context.Row.index;
      `%FStar.Pervasives.coerce_eq;
    ]
  ];
  Tac.trefl ()

let tac_extract_full_generic (namespaces: list string) (local_delta: list string) () =
  let base_delta = [
    "Pipit.Exec.Pulse.mk_step_pure";
    "Pipit.Context.Row.index";
    "FStar.Pervasives.coerce_eq"
  ] in
  let opts ns = [
    nbe;
    primops;
    iota;
    zeta;
    delta_namespace ("Pipit" :: "FStar.Pervasives" :: ns);
    delta_only (local_delta @ base_delta);
    delta_qualifier ["inline_for_extraction"];
    delta_attr [`%Pipit.Tactics.norm_attr]
  ] in
  Tac.norm (opts namespaces);
  Tac.trefl ()

let tac_specialize_generic (namespaces: list string) (local_delta: list string) () =
  Tac.norm [
    zeta;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only (local_delta @ [
      "Pipit.Exec.Pulse.mk_init";
      "Pipit.Exec.Pulse.mk_step_pure";
      "Pipit.Exec.Pulse.mk_reset";
      "Pipit.Exec.Pulse.mk_step";
      "Pipit.Exec.Pulse.mk_reset_sys";
      "Pipit.Exec.Pulse.mk_step_sys";
      "Pipit.Context.Row.index";
      "FStar.Pervasives.coerce_eq"
    ])
  ];
  Tac.trefl ()

let tac_extract_full_strong_generic (namespaces: list string) (local_delta: list string) () =
  tac_extract_full_strong_core namespaces local_delta;
  Tac.trefl ()

let tac_specialize_strong_generic (namespaces: list string) (local_delta: list string) () =
  let base_delta = [
    "Pipit.Exec.Pulse.mk_init";
    "Pipit.Exec.Pulse.mk_step_pure";
    "Pipit.Exec.Pulse.mk_reset";
    "Pipit.Exec.Pulse.mk_step";
    "Pipit.Exec.Pulse.mk_reset_sys";
    "Pipit.Exec.Pulse.mk_step_sys";
    "Pipit.Context.Row.index";
    "FStar.Pervasives.coerce_eq"
  ] in
  Tac.norm [
    zeta;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only (local_delta @ base_delta)
  ];
  Tac.norm [
    zeta_full;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only local_delta
  ];
  Tac.trefl ()


(* ====================================================================== *)
(*  Strict, fail-loud specialisation                                       *)
(* ====================================================================== *)

(* Baseline set of fully-qualified names that must NOT appear in a Pipit
  extraction body after normalization.

  The set is a contract: each FQN here is a recursive row-traversal
  helper that must be specialised on the concrete context
  ([Pipit.Context.Row.index]), a witness coercion that becomes a
  [coerce_eq__any_any] hole in C if it survives
  ([FStar.Pervasives.coerce_eq]), or a Pipit core AST type / constructor
  that should have been fully evaluated away by the symbolic
  interpreter ([state_of_exp] / [exec_of_exp]) — if one of these AST
  nodes survives, extraction is broken and we want to fail loudly,
  not silently produce a [<: any] cast downstream in KaRaMeL.

  Notably absent: the Pulse [mk_*] wrappers. They are
  [inline_for_extraction] and KaRaMeL inlines them downstream; if F*'s
  normalizer leaves them unreduced (as it does for Pulse [fn] bodies
  in spec positions, see Warning 249 "Losing precision when encoding a
  function literal") that is OK. The legacy [tac_extract] used to list
  them in [delta_only], but only as a *hint*: a surviving [mk_init] in
  the final term was never a real bug. *)
let base_specialize_forbidden: list string = [
  (* Row + coercion *)
  "Pipit.Context.Row.index";
  "FStar.Pervasives.coerce_eq";
  (* Core exp / exp_apps / exp_base types *)
  `%PEB.exp;
  `%PEB.exp_apps;
  `%PEB.exp_base;
  (* exp constructors *)
  `%PEB.XBase;
  `%PEB.XApps;
  `%PEB.XFby;
  `%PEB.XMu;
  `%PEB.XLet;
  `%PEB.XContract;
  `%PEB.XCheck;
  (* exp_apps constructors *)
  `%PEB.XPrim;
  `%PEB.XApp;
  (* exp_base constructors *)
  `%PEB.XVal;
  `%PEB.XBVar;
  `%PEB.XVar;
]

(* Pulse / row helpers that the normalizer should TRY to unfold (they
  are listed in [delta_only]) but whose surviving presence in the goal
  is NOT a strictness violation. Mostly the [mk_*] inline wrappers and
  the row/coerce helpers, which KaRaMeL inlines downstream if F*'s
  normalizer cannot. *)
let base_specialize_delta_only: list string = [
  `%mk_init;
  `%mk_step_pure;
  `%mk_reset;
  `%mk_step;
  `%mk_reset_sys;
  `%mk_step_sys;
  "Pipit.Context.Row.index";
  "FStar.Pervasives.coerce_eq";
]

(* Run [Tac.norm] with the Pipit / Pulse normalization options.

  Two different option sets, gated by [use_nbe]:

  ## Pure mode ([use_nbe = true])

  Targets the pure [state] / [system] bodies, which recurse over the
  symbolic [exp] AST via [state_of_exp] / [exec_of_exp]. We want
  aggressive unfolding so the recursion fully evaluates:

  - [nbe; primops; iota; zeta_full] — NBE for stack-safe deep recursion.
  - [delta_namespace ("Pipit" :: "FStar.Pervasives" :: ... :: namespaces)]
    unfolds Pipit core (including [exec_of_exp]), F* prelude, and the
    user-supplied source / target modules.
  - [delta_only forbidden] forces the listed FQNs to unfold even if
    they live outside the namespace list.
  - [delta_qualifier ["inline_for_extraction"]] inlines the [mk_*]
    helpers and the splice-emitted [<nm>_system] wrapper.
  - [delta_attr [...]] mirrors [Pipit.Tactics.norm_full]: unfolds
    [@@norm_attr], the [core_lifted] / [core_lifted_prim] splice
    outputs, and typeclass instance dictionaries.

  ## Pulse mode ([use_nbe = false])

  Targets the Pulse [reset] / [step] bodies. Mirrors the legacy
  [tac_extract] options almost verbatim, because:

  - NBE on Pulse-shaped terms triggers [NBE ill-typed application:
    Unknown] on [Inline_for_extraction; NoExtract] [<nm>_system]
    wrappers, so it is disabled.
  - Unfolding [Pipit.Exec.Exp.exec_of_exp] without NBE leaves stuck
    residue (recursive matches that do not iota-reduce), and the
    elaborator subsequently emits [Tm_unknown] when typechecking the
    sigelt's inferred type. So [delta_namespace] is restricted to the
    user-supplied namespaces — [exec_of_exp] stays opaque, exactly as
    it was under legacy [tac_extract].
  - [delta_qualifier] / [delta_attr] are likewise omitted: the
    [<nm>_system] wrapper is already in the user namespaces (the target
    module of the splice) so it unfolds via [delta_namespace], and we
    do not want typeclass instances to expand inside Pulse spec
    fragments. *)
let specialize_norm_opts
  (use_nbe: bool)
  (namespaces: list string)
  (delta_only_extra: list string)
  : list norm_step
=
  let delta_only_all = L.append delta_only_extra base_specialize_delta_only in
  if use_nbe then [
    nbe;
    primops;
    iota;
    zeta_full;
    delta_namespace
      ("Pipit" :: "FStar.Pervasives" :: "FStar.List" :: "FStar.Option"
        :: "FStar.Seq" :: namespaces);
    delta_only delta_only_all;
    delta_qualifier ["inline_for_extraction"];
    delta_attr [
      `%Pipit.Tactics.norm_attr;
      "Pipit.Plugin.Interface.core_lifted";
      "Pipit.Plugin.Interface.core_lifted_prim";
      "Pipit.Plugin.Interface.core_lifted_ctx";
      `%FStar.Tactics.Typeclasses.tcinstance
    ]
  ] else [
    primops;
    iota;
    zeta_full;
    delta_namespace namespaces;
    delta_only delta_only_all;
  ]

(* Iterative, fail-loud specialiser.

  Repeatedly normalises the current goal with [specialize_norm_opts] and
  then walks the resulting term to count occurrences of any FQN in
  [base_specialize_forbidden @ extra]. Behaviour:

    * Surviving count drops to 0 -> [trefl ()], done.
    * Surviving count does not decrease compared to the previous round
      -> fail with the surviving names.
    * [fuel_cap] iterations elapse without convergence -> fail with the
      surviving names.

  In practice the F* normaliser is already a fixed-point algorithm, so
  one or two iterations suffice. The loop exists as cheap insurance for
  cases where typeclass-instance resolution or layered ascriptions
  prevent a single pass from reaching the true fixed point.

  Designed to be installed via [FStar.Tactics.postprocess_with] on
  extracted bindings.

  The [delta_only] list passed to the normalizer is
  [base_specialize_delta_only] (Pulse [mk_*] wrappers, row/coerce
  helpers); the forbidden-FQN check uses the disjoint
  [base_specialize_forbidden] (true bugs: surviving AST nodes,
  unspecialised row traversals, residual coercions). [extra] is added
  to BOTH — splice-emitted helpers like [<nm>_system] are both forced
  to unfold and required to be gone after normalization.

  Parameters:
    * [use_nbe]: see [specialize_norm_opts]. Use [true] for pure
      [state]/[system] bodies; [false] for Pulse [reset]/[step] bodies.
    * [namespaces]: extra module namespaces to unfold (typically the
      source and target modules of the splice).
    * [extra]: additional FQNs that must (a) be unfolded and (b) not
      survive normalization; used for module-local helpers
      ([<nm>_system], [<nm>_step_apply], etc.).
    * [fuel_cap]: maximum number of [norm] iterations before giving up. *)
let tac_specialize_strict_with
  (use_nbe: bool)
  (namespaces: list string)
  (extra: list string)
  (fuel_cap: nat)
  ()
  : Tac.Tac unit
=
  let forbidden = L.append extra base_specialize_forbidden in
  let opts = specialize_norm_opts use_nbe namespaces extra in
  let report (kind: string) (surv: list string): Tac.Tac unit =
    let header = "tac_specialize_strict: " ^ kind
      ^ "; the following forbidden FQN(s) still appear in the goal:\n  - " in
    Tac.fail (header ^ S.concat "\n  - " surv)
  in
  let rec loop (remaining: nat) (prev: option nat): Tac.Tac unit =
    Tac.norm opts;
    let surv = PTB.term_collect_fqns forbidden (Tac.cur_goal ()) in
    let cnt = L.length surv in
    if cnt = 0 then Tac.trefl ()
    else (
      let no_progress = match prev with
        | None -> false
        | Some p -> cnt >= p
      in
      if remaining = 0 then report "fuel exhausted" surv
      else if no_progress then report "no progress" surv
      else loop (remaining - 1) (Some cnt)
    )
  in
  loop fuel_cap None

(* Strict specialiser for pure [state] / [system] sigelts (uses NBE). *)
let tac_specialize_strict_pure (namespaces: list string) (extra: list string) ()
  : Tac.Tac unit
=
  tac_specialize_strict_with true namespaces extra 8 ()

(* Strict specialiser for Pulse [reset] / [step] sigelts (no NBE). *)
let tac_specialize_strict_pulse (namespaces: list string) (extra: list string) ()
  : Tac.Tac unit
=
  tac_specialize_strict_with false namespaces extra 8 ()

(* Debug variant of [tac_specialize_strict_pulse]: dumps the goal both
  BEFORE any normalization and AFTER the first [Tac.norm] pass, then
  finishes with [trefl] regardless of whether forbidden FQNs survive.
  Use from a manual extraction file to inspect what the normalizer
  actually leaves behind. *)
let tac_specialize_strict_pulse_debug (namespaces: list string) (extra: list string) ()
  : Tac.Tac unit
=
  let opts = specialize_norm_opts false namespaces extra in
  let goal_before = Tac.cur_goal () in
  Tac.print ("tac_specialize_strict_pulse_debug: BEFORE norm: "
    ^ Tac.term_to_string goal_before);
  Tac.norm opts;
  let goal_after = Tac.cur_goal () in
  Tac.print ("tac_specialize_strict_pulse_debug: AFTER norm: "
    ^ Tac.term_to_string goal_after);
  let forbidden = L.append extra base_specialize_forbidden in
  let surv = PTB.term_collect_fqns forbidden goal_after in
  Tac.print ("tac_specialize_strict_pulse_debug: surviving forbidden FQNs: ["
    ^ S.concat "; " surv ^ "]");
  Tac.trefl ()

(* Same as [tac_specialize_strict_pulse_debug] but for the pure variant. *)
let tac_specialize_strict_pure_debug (namespaces: list string) (extra: list string) ()
  : Tac.Tac unit
=
  let opts = specialize_norm_opts true namespaces extra in
  let goal_before = Tac.cur_goal () in
  Tac.print ("tac_specialize_strict_pure_debug: BEFORE norm: "
    ^ Tac.term_to_string goal_before);
  Tac.norm opts;
  let goal_after = Tac.cur_goal () in
  Tac.print ("tac_specialize_strict_pure_debug: AFTER norm: "
    ^ Tac.term_to_string goal_after);
  let forbidden = L.append extra base_specialize_forbidden in
  let surv = PTB.term_collect_fqns forbidden goal_after in
  Tac.print ("tac_specialize_strict_pure_debug: surviving forbidden FQNs: ["
    ^ S.concat "; " surv ^ "]");
  Tac.trefl ()

