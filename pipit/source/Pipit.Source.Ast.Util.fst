(* Shared helpers between `Pipit.Source.Ast.Reflect` and
   `Pipit.Source.Ast.Lower`. Kept separate so neither pass needs to
   import the other just to reuse a small utility. *)
module Pipit.Source.Ast.Util

module T   = FStar.Tactics.V2
module Ref = FStar.Reflection.V2
module L   = FStar.List.Tot

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface
module PTB = Pipit.Tactics.Base

(* Drop implicit / typeclass-instance binders, keep explicit ones in
   declaration order. *)
let explicit_binders (bs: list T.binder): list T.binder =
  L.filter (fun (b: T.binder) -> Ref.Q_Explicit? b.qual) bs

(* Build a unique AST name from a `T.namedv`. The uniq is part of the
   string so distinct binders with the same surface ppname don't clash. *)
let mk_uniq_ast_name (nv: T.namedv): T.Tac Ast.name =
  let ppname = T.unseal nv.ppname in
  ppname ^ "#" ^ string_of_int nv.uniq

(* For a data constructor [ctor], return the ppnames of its explicit
   binders -- exactly the field names used by F*'s auto-generated
   projectors ([Mktuple2?._1], [Mkpoint?.px], [Some?.v], etc.). *)
let ctor_field_names (env: T.env) (ctor_fv: T.fv): T.Tac (list Ast.name) =
  let ctor_tm = T.pack (T.Tv_FVar ctor_fv) in
  let ctor_ty = T.tc env ctor_tm in
  let (bs, _) = T.collect_arr_bs ctor_ty in
  T.map (fun (b: T.binder) -> T.unseal b.ppname) (explicit_binders bs)

(* Recover the implicit type arguments threaded through a scrutinee's
   type. For [tuple2 int int] the head is the type constructor and the
   args are [int; int]; we re-tag as implicit so they instantiate the
   projector's [#a -> #b -> ...] binders. *)
let scrut_type_implicits (scrut_ty: T.term): T.Tac (list T.argv) =
  let (_, ty_args) = T.collect_app scrut_ty in
  T.map (fun (a: T.argv) -> let (t, _) = a in (t, T.Q_Implicit)) ty_args

(* Compute the FQN of F*'s auto-generated projector for a constructor's
   explicit field: replace the last segment `Ctor` of [ctor_fqn] with
   `__proj__Ctor__item__field`. *)
let projector_fqn (ctor_fqn: Ast.fqn) (field: Ast.name): T.Tac Ast.fqn =
  match L.rev ctor_fqn with
  | [] -> T.fail "Pipit.Source.Ast.Util: empty constructor FQN"
  | ctor_nm :: rest_rev ->
    let proj_nm = "__proj__" ^ ctor_nm ^ "__item__" ^ field in
    L.rev (proj_nm :: rest_rev)

(* Peel leading implicit (`explicit=false`) `ModeFun` layers off a mode.
   Used by callers that walk an arg list and only want one mode layer
   per EXPLICIT argument. *)
let rec skip_implicit_modes (m: PPI.mode): PPI.mode =
  match m with
  | PPI.ModeFun _ false rm -> skip_implicit_modes rm
  | _ -> m


(* Does sigelt [se] carry attribute [`%PPI.core_of_source nm _]
   matching source FQN string [nm_src_fqn]? *)
let sigelt_core_of_source_matches
  (se: Ref.sigelt)
  (nm_src_fqn: string)
: T.Tac bool
=
  let rec go (attrs: list T.term): T.Tac bool =
    match attrs with
    | [] -> false
    | hd :: tl ->
      let (h, args) = T.collect_app hd in
      if PTB.term_check_fv h (`%PPI.core_of_source) then
        (match args with
         | (arg, _) :: _ ->
           (match T.inspect arg with
            | T.Tv_Const (Ref.C_String s) ->
              if s = nm_src_fqn then true else go tl
            | _ -> go tl)
         | _ -> go tl)
      else go tl
  in
  go (Ref.sigelt_attrs se)

(* Find the core binding for source FQN [nm_src_fqn] by attribute
   lookup. Returns the FQN of the chosen core binding.

   Both the auto-generated `<nm>_core` splice (emitted by
   `Pipit.Plugin.Lift.lift_ast_tac`) and any blessed wrapper
   (e.g. a `body_contract` that re-wraps the core in `XContract` +
   `bless`, or the `__check_<id>` synthesised by `[@@proof_induct1]`)
   can carry the `[@@core_of_source nm _]` attribute. When multiple
   candidates exist we pick the one defined latest in scope: F*'s
   attribute table cons'es each new sigelt to the front of the result
   of `Ref.lookup_attr`, so `List.hd` is the most recently defined
   binding (matching the usual F* shadowing convention "later
   definition wins"). Wrappers are emitted *after* the raw
   `<id>_core` splice, so they win automatically.

   Wrappers must also be tagged `[@@core_lifted]` so that
   `Pipit.Tactics.norm_full` can unfold them during caller-side
   induction; otherwise the dispatch routes through an opaque binding
   and normalisation gets stuck.

   This is the single source of truth for source -> core dispatch.
   Callers should pass through here rather than munging names with a
   `_core` suffix. *)
let find_core_for_source
  (tac_env: T.env)
  (nm_src_fqn: string)
: T.Tac Ast.fqn
=
  let cof_fvs = Ref.lookup_attr (`PPI.core_of_source) tac_env in
  let classify (fv: Ref.fv): T.Tac (option Ref.name) =
    let nm = T.inspect_fv fv in
    match T.lookup_typ tac_env nm with
    | None -> None
    | Some se ->
      if sigelt_core_of_source_matches se nm_src_fqn
      then Some nm
      else None
  in
  let candidates = T.filter_map classify cof_fvs in
  match candidates with
  | nm :: _ -> nm
  | [] ->
    T.fail ("Pipit.Source.Ast.Util.find_core_for_source: no core binding "
            ^ "tagged [@@core_of_source \"" ^ nm_src_fqn
            ^ "\"] in scope. Did the source binding get lifted via "
            ^ "[%splice[] (PPL.lift_ast_tac1 \"...\")]?")
