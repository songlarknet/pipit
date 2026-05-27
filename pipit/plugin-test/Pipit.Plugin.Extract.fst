(* Splice helper that generates the per-binding boilerplate for extracting
  a Pipit stream function to a transition system plus Pulse [reset]/[step].

  Usage:
    [%splice [ count_when_state; __extractable_count_when;
               count_when_system; count_when_reset; count_when_step ]
      (Pipit.Plugin.Extract.extract `%count_when)]

  The single argument is the fully-qualified name of the source binding
  (the form `[`%nm]` produces this string at typecheck time). The splice
  produces five top-level bindings in the splicing module:

    [<nm>_state]           : Type
    [__extractable_<nm>]   : squash (extractable (SL.simplify __core_<nm>))
    [<nm>_system]          : XX.esystem (<input-row>) <nm>_state <result-ty>
    [<nm>_reset]           : Pulse reset function
    [<nm>_step]            : Pulse step function

  Listing all five names gives F* a typo guard: the splice fails at
  elaboration time if any declared name is not produced. The empty
  bracket list [[]] is also accepted (F* only checks that every declared
  name is actually produced, so [[]] simply skips the check) but loses
  that guard; prefer the explicit form.

  The input row and result types are inferred from the source binding's
  arrow type by stripping the [stream] type constructor. Multiple stream
  inputs are supported: for [f (a: stream A) (b: stream B): stream R] the
  generated [<nm>_step] takes [a] and [b] as separate arguments, the
  internal input row is [A & (B & unit)], and the system is
  [XX.esystem (A & (B & unit)) <nm>_state R]. *)
module Pipit.Plugin.Extract

module Tac = FStar.Tactics.V2
module Ref = FStar.Reflection.V2

module List = FStar.List.Tot

module PTB = Pipit.Tactics.Base

module SL  = Pipit.Exp.SimplifyLet
module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.Pulse
module PT  = Pipit.Tactics


(* -------------------------------------------------------------------- *)
(* Helpers                                                              *)
(* -------------------------------------------------------------------- *)

(* Strip a [stream X] application down to [X].

  Reflected stream types come in as [stream #has_stream_X X] (the dictionary
  argument is implicit). We recognise the head as any fully-qualified name
  ending in ["stream"] and return the last explicit argument. *)
let strip_stream (t: Tac.term): Tac.Tac Tac.term =
  let (head, args) = Tac.collect_app t in
  let is_stream =
    match Tac.inspect head with
    | Tac.Tv_FVar fv | Tac.Tv_UInst fv _ ->
      (match List.rev (Tac.inspect_fv fv) with
        | "stream" :: _ -> true
        | _ -> false)
    | _ -> false
  in
  if is_stream
  then (
    match List.rev args with
    | (v, Tac.Q_Explicit) :: _ -> v
    | _ -> Tac.fail ("Pipit.Plugin.Extract.strip_stream: no explicit arg in "
                    ^ Tac.term_to_string t)
  ) else t

(* Last element of a list (tactic-fails on empty). *)
let rec list_last #a (xs: list a): Tac.Tac a =
  match xs with
  | [] -> Tac.fail "list_last: empty"
  | [x] -> x
  | _ :: tl -> list_last tl

(* Everything but the last element. *)
let rec list_init #a (xs: list a): Tac.Tac (list a) =
  match xs with
  | [] -> Tac.fail "list_init: empty"
  | [_] -> []
  | x :: tl -> x :: list_init tl

(* Split a (post-plugin) source-binding type into stripped inputs and a
  stripped result type. Each input carries its source ppname (for the
  generated step function's parameter names) alongside its stripped type. *)
let split_stream_arrow (ty: Tac.term): Tac.Tac (list (string & Tac.term) & Tac.term) =
  let binders, comp = Tac.collect_arr_bs ty in
  let result =
    match comp with
    | Tac.C_Total r | Tac.C_GTotal r -> r
    | _ -> Tac.fail "split_stream_arrow: expected pure arrow result"
  in
  let inputs =
    Tac.map
      (fun (b: Tac.binder) -> Tac.name_of_binder b, strip_stream b.sort)
      binders
  in
  inputs, strip_stream result

(* Right-nested product type [t1 & (t2 & ... & (tN & unit))]; [[]] -> [unit]. *)
let rec mk_input_row_ty (tys: list Tac.term): Tac.Tac Tac.term =
  match tys with
  | [] -> `unit
  | t :: rest ->
    let r = mk_input_row_ty rest in
    `((`#t) & (`#r))

(* Right-nested tuple expression [(v1, (v2, ..., (vN, ())))]; [[]] -> [()]. *)
let rec mk_input_tuple (vs: list Tac.term): Tac.Tac Tac.term =
  match vs with
  | [] -> `()
  | v :: rest ->
    let r = mk_input_tuple rest in
    `((`#v, `#r))


(* -------------------------------------------------------------------- *)
(* Sigelt construction                                                  *)
(* -------------------------------------------------------------------- *)

(* Pack a non-recursive [let nm : ty = body] sigelt with the supplied
  qualifiers and attributes. Use [Tac.pack Tac.Tv_Unknown] for [ty] to
  let F* infer it. *)
let mk_let_sigelt
  (nm: Ref.name)
  (ty: Tac.term)
  (body: Tac.term)
  (quals: list Ref.qualifier)
  (attrs: list Tac.term)
  : Tac.Tac Tac.sigelt
=
  let lb: Tac.letbinding = {
    lb_fv  = Tac.pack_fv nm;
    lb_us  = [];
    lb_typ = ty;
    lb_def = body;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let { isrec = false; lbs = [lb] } in
  let se = Tac.pack_sigelt sv in
  let se = Ref.set_sigelt_quals quals se in
  Ref.set_sigelt_attrs attrs se


(* -------------------------------------------------------------------- *)
(* Main entry point                                                     *)
(* -------------------------------------------------------------------- *)

(* Generate the four extraction sigelts for the source binding [nm_src_fqn]
  (a fully-qualified name like ["Plugin.Test.Example.Simple.Check.count_when"]).

  The lifted core expression is expected to live at [<src-module>.__core_<nm>]
  in the same module as the source binding (this is what the [#lang-pipit]
  preprocessor emits). *)
let extract (nm_src_fqn: string): Tac.Tac (list Tac.sigelt) =
  let tac_env = Tac.top_env () in
  let src_qn = Ref.explode_qn nm_src_fqn in
  let src_short = list_last src_qn in
  let src_module = list_init src_qn in

  (* The lifted core expression name in the source module. *)
  let core_short = "__core_" ^ src_short in
  let core_qn = List.append src_module [core_short] in
  let core_fqn = Ref.implode_qn core_qn in

  (* Sanity-check that [__core_<nm>] exists; raise an actionable error
    otherwise. *)
  (match Ref.lookup_typ tac_env core_qn with
    | None ->
      Tac.fail ("Pipit.Plugin.Extract.extract: cannot find lifted core binding ["
                ^ core_fqn ^ "]; is the source module using [#lang-pipit] and "
                ^ "does it define [" ^ src_short ^ "]?")
    | Some _ -> ());

  (* Inspect the source binding's type to discover input / output types. *)
  let src_lb = PTB.lookup_lb_top tac_env src_qn in
  let inputs, result_ty = split_stream_arrow src_lb.lb_typ in

  (* Zero-input stream functions don't have a meaningful step signature. *)
  (match inputs with
    | [] ->
      Tac.fail ("Pipit.Plugin.Extract.extract: source binding "
                ^ nm_src_fqn ^ " has no stream inputs")
    | _ -> ());

  (* Build a fresh namedv per input so we can refer to it in both the
    abstraction (binder) and the body (variable). Source ppnames are
    preserved so the generated step function uses the same parameter names
    as the source binding. *)
  let input_nvs: list (Tac.namedv & Tac.term) =
    Tac.map
      (fun (nm, ty) ->
        let nv: Tac.namedv = {
          uniq   = Tac.fresh ();
          sort   = Tac.seal ty;
          ppname = Ref.as_ppname nm;
        } in
        nv, ty)
      inputs
  in
  let input_tys = Tac.map (fun (_, ty) -> ty) input_nvs in
  (* The Pipit lifter pushes binders innermost-first, so the row's
    head ([Row.index 0]) corresponds to the LAST source argument. Reverse
    the source-order input list when building the row type and the value
    we hand to [mk_step_pure]. The N-arg abstraction itself stays in source
    order so the generated [<nm>_step] takes parameters in the same order
    as the source binding. *)
  let input_tys_rev = Tac.fold_left (fun acc t -> t :: acc) [] input_tys in

  (* The namespace passed to [tac_normalize_pure] / [tac_extract]: covers
    both the source module (so [__core_*] and [__prim_*] unfold) and the
    target module (so the splice-emitted [<nm>_system] unfolds inside
    [<nm>_reset] / [<nm>_step]). *)
  let ns_term: Tac.term =
    let mk_str s = Tac.pack (Tac.Tv_Const (Ref.C_String s)) in
    let src_str = mk_str (Ref.implode_qn src_module) in
    let tgt_str = mk_str (Ref.implode_qn (Tac.cur_module ())) in
    `(Cons #string (`#src_str) (Cons #string (`#tgt_str) (Nil #string)))
  in

  (* The lifted core expression term, e.g. [Plugin.Test.Example.Simple.Check.__core_count_when]. *)
  let core_term: Tac.term =
    Tac.pack (Tac.Tv_FVar (Tac.pack_fv core_qn))
  in

  (* The "simplified" core expression used as the argument to [state_of_exp]
    and [exec_of_exp]. *)
  let expr_term: Tac.term = `(SL.simplify (`#core_term)) in

  (* Fully-qualified names of the bindings we are about to define, so later
    sigelts can refer back to earlier ones. *)
  let tgt_module = Tac.cur_module () in
  let state_qn  = List.append tgt_module [src_short ^ "_state"] in
  let system_qn = List.append tgt_module [src_short ^ "_system"] in
  let reset_qn  = List.append tgt_module [src_short ^ "_reset"] in
  let step_qn   = List.append tgt_module [src_short ^ "_step"] in
  (* Auxiliary proof binding referenced from [<nm>_system]; see comment
    on [system_body] below. *)
  let proof_qn  = List.append tgt_module ["__extractable_" ^ src_short] in
  let state_term  = Tac.pack (Tac.Tv_FVar (Tac.pack_fv state_qn)) in
  let system_term = Tac.pack (Tac.Tv_FVar (Tac.pack_fv system_qn)) in
  let proof_term  = Tac.pack (Tac.Tv_FVar (Tac.pack_fv proof_qn)) in

  (* Common attribute: postprocess with [tac_normalize_pure]. *)
  let attr_norm: Tac.term =
    `(FStar.Tactics.postprocess_with (XL.tac_normalize_pure (`#ns_term)))
  in
  let attr_extract: Tac.term =
    `(FStar.Tactics.postprocess_with
        (XL.tac_extract (`#ns_term)))
  in

  (* ---- state ---- *)
  let state_body: Tac.term = `(XX.state_of_exp (`#expr_term)) in
  let state_ty: Tac.term = `Type0 in
  let se_state = mk_let_sigelt state_qn state_ty state_body [] [attr_norm] in

  (* ---- system ---- *)
  let input_row: Tac.term = mk_input_row_ty input_tys_rev in
  let system_ty: Tac.term =
    `(XX.esystem (`#input_row) (`#state_term) (`#result_ty))
  in
  (* ---- extractable proof ----
    We need [extractable expr = true] available as an SMT hypothesis when
    the typechecker checks the [exec_of_exp expr] call inside [<nm>_system].
    The refinement is opaque under the irreducible [core_lifted] attribute
    on [__core_*], so we discharge it explicitly.

    Approach: emit a dedicated top-level binding whose body is built via
    [synth_by_tactic] at type [squash (extractable expr)]. F* runs the
    tactic at elaboration to produce the witness; the tactic normalises
    [extractable expr] to [true] then closes the resulting goal (after
    [synth_by_tactic]'s wrapping the goal is [squash (squash l_True)],
    which is inhabited by [()]).

    The binding is then referenced via a lambda binder from [<nm>_system]
    (see [system_body] below). Inlining the [synth_by_tactic] call into
    [system_body] does NOT work: the typechecker tries to discharge
    [extractable expr] on the [exec_of_exp] call before it has finished
    elaborating the [synth_by_tactic] witness argument, so the hypothesis
    is not yet in scope. Splitting into two sigelts forces F* to fully
    elaborate the witness first. *)
  let extractable_prop: Tac.term =
    `(squash (XX.extractable (`#expr_term)))
  in
  let proof_body: Tac.term =
    `(FStar.Tactics.Effect.synth_by_tactic
        #(`#extractable_prop)
        (fun () ->
          PT.norm_full (`#ns_term);
          FStar.Tactics.V2.exact (`())))
  in
  let se_proof =
    mk_let_sigelt proof_qn extractable_prop proof_body [Ref.NoExtract] []
  in

  (* ---- system ----
    Body shape:
      [(fun (_: squash (extractable expr)) -> exec_of_exp expr)
         __extractable_<nm>]

    Why the lambda+application: bringing [squash (extractable expr)] into
    scope via a lambda binder gives the typechecker the SMT hypothesis it
    needs to discharge the refinement on [exec_of_exp]'s argument. A
    [let _: T = ... in ...] would be more idiomatic but antiquotations do
    not parse cleanly inside [let]-binder type annotations in the [`(...)]
    quasiquote. *)
  let system_body: Tac.term =
    `((fun (_: squash (XX.extractable (`#expr_term))) ->
         XX.exec_of_exp (`#expr_term))
        (`#proof_term))
  in
  let se_system =
    mk_let_sigelt system_qn system_ty system_body
      [Ref.NoExtract; Ref.Inline_for_extraction]
      [attr_norm]
  in

  (* ---- reset ---- *)
  let reset_body: Tac.term = `(XL.mk_reset (XL.mk_init (`#system_term))) in
  let reset_ty: Tac.term = Tac.pack Tac.Tv_Unknown in
  let se_reset = mk_let_sigelt reset_qn reset_ty reset_body [] [attr_extract] in

  (* ---- step ----
    Body shape for N inputs:
      [fun (a1: t1) ... (aN: tN) ->
         XL.mk_step
           (fun i st -> XL.mk_step_pure system i st)
           (aN, (aN-1, ..., (a1, ())))]

    The N-arg abstraction follows source order so the generated step
    function takes parameters in the same order as the source binding.
    The row passed to [mk_step_pure] is REVERSED because the Pipit lifter
    pushes binders innermost-first ([Row.index 0] = last source argument).

    Built bottom-up: the inner [mk_step] call references each binder via
    [Tv_Var] in reversed order, then [Tv_Abs] is folded right-to-left
    over the source-order binders. *)
  let input_vars_rev: list Tac.term =
    Tac.fold_left
      (fun acc (nv, _) -> Tac.pack (Tac.Tv_Var nv) :: acc)
      [] input_nvs
  in
  let input_tuple: Tac.term = mk_input_tuple input_vars_rev in
  let step_call: Tac.term =
    `(XL.mk_step
        (fun i st -> XL.mk_step_pure (`#system_term) i st)
        (`#input_tuple))
  in
  let step_body: Tac.term =
    Tac.fold_right
      (fun (nv, ty) body ->
        Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder nv ty) body))
      input_nvs step_call
  in
  let step_ty: Tac.term = Tac.pack Tac.Tv_Unknown in
  let se_step = mk_let_sigelt step_qn step_ty step_body [] [attr_extract] in

  [se_state; se_proof; se_system; se_reset; se_step]
