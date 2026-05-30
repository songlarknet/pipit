(* Shared helpers between `Pipit.Source.Ast.Reflect` and
   `Pipit.Source.Ast.Lower`. Kept separate so neither pass needs to
   import the other just to reuse a small utility. *)
module Pipit.Source.Ast.Util

module T   = FStar.Tactics.V2
module Ref = FStar.Reflection.V2
module L   = FStar.List.Tot

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface

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
