(* Lower a `Pipit.Source.Ast.ast` to a checked core expression over the
   shallow primitive table (`Pipit.Prim.Shallow.table`).

   Stage A — tactic-driven term builder. `lower` returns a quoted F*
   term that, after splicing and re-typechecking, has type:

     exp Pipit.Prim.Shallow.table ctx rty

   (`exp`, not `cexp`, for now — blessing to `cexp` is left to the
   splice site so that we can iterate on Lower without paying for
   `check_all` discharge on every change.)

   The Lower pass is specialised to `Pipit.Prim.Shallow.table`. If/when
   another backend table is needed, a sibling module under
   `Pipit.Source.Ast.Lower.*` can target it, sharing the same AST.

   Strategy
   --------
   * Lower is split into two mutually recursive helpers:
       `lower_stream` — produces an `exp t c ty`
       `lower_static` — produces a static F* term of the source type
     so each case knows what it's emitting.
   * `Stream` binders live in the cexp context (de Bruijn). `AVar n Stream`
     resolves to `XBVar idx` where `idx` is the number of stream binders
     between `n` and the innermost binding.
   * `Static` binders live as ordinary F* term variables (`namedv`).
     `AVar n Static` resolves to a `Tv_Var` of the stored `namedv`.
   * When a static value is consumed in stream context, it is lifted via
     `XVal`. Going the other way (stream -> static) is a hard error.
*)
module Pipit.Source.Ast.Lower

module T   = FStar.Tactics.V2
module R   = FStar.Reflection.V2
module L   = FStar.List.Tot

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface
module PPS = Pipit.Prim.Shallow
module PPT = Pipit.Prim.Table
module PXB = Pipit.Exp.Base
module PM  = Pipit.Prop.Metadata
module PSSB = Pipit.Prim.HasStream
module PTB = Pipit.Tactics.Base

(*** Lowering environment ***)

(* How a binder was introduced. *)
noeq
type binder_kind =
  (* Bound in the cexp context. Its de Bruijn index is recovered by
     counting the number of `BStream` binders that came after it. *)
  | BStream
  (* Bound as a real F* term variable at the splice site. *)
  | BStatic: nv: T.namedv -> binder_kind

noeq
type binder = {
  b_name: Ast.name;
  b_sty:  Ast.sty;
  b_kind: binder_kind;
}

(* Lowering environment: binders in scope (innermost first), plus an
   `inst_for` callback used to materialise `has_stream` typeclass
   instances for source types. The callback is supplied by the splice
   driver (`Pipit.Plugin.Lift`) so that polymorphic source bindings can
   thread local instance binders into the spliced term without relying
   on F*'s implicit-uvar machinery (which loses the local env for
   sigelts built via `Tv_App`/quasi-quote). Returning `None` falls back
   to the quasi-quote `PSSB.shallow sty` form (works for ground types). *)
noeq
type lower_env = {
  binders: list binder;
  inst_for: T.term -> T.Tac (option T.term);
}

let empty_env: lower_env = {
  binders = [];
  inst_for = (fun _ -> None);
}

let env_push (b: binder) (env: lower_env): lower_env =
  { env with binders = b :: env.binders }

(* Compute the de Bruijn index of a stream-bound name. Returns `None`
   if the name isn't a stream binder or isn't in scope. *)
let rec env_bvar_index (n: Ast.name) (bs: list binder): option nat =
  match bs with
  | [] -> None
  | b :: bs' ->
    if b.b_name = n
    then (match b.b_kind with | BStream -> Some 0 | _ -> None)
    else
      (match env_bvar_index n bs' with
       | None -> None
       | Some i ->
         (match b.b_kind with
          | BStream -> Some (i + 1)
          | BStatic _ -> Some i))

(* Look up a binder by name. *)
let rec env_lookup (n: Ast.name) (bs: list binder): option binder =
  match bs with
  | [] -> None
  | b :: bs' -> if b.b_name = n then Some b else env_lookup n bs'

(* Extract just the stream binders' source types from an env binder
   list, preserving innermost-first order. Used to build a caller-side
   cexp context when calling another lifted binding. *)
let rec stream_ctx_of_binders (bs: list binder): list Ast.sty =
  match bs with
  | [] -> []
  | b :: rest ->
    (match b.b_kind with
     | BStream -> b.b_sty :: stream_ctx_of_binders rest
     | BStatic _ -> stream_ctx_of_binders rest)

(*** Term builders ***)

(* Build the shallow type term for a source type: `PSSB.shallow #ty`.
   Relies on typeclass resolution at splice time to pick the right
   `has_stream` instance. Works for ground types (`int`, `bool`, ...)
   because F* resolves them globally regardless of env. For
   type-variable / polymorphic uses where the instance must come from a
   local binder, the caller must provide the instance term explicitly
   (see `shallow_ty_with_inst` and `Pipit.Plugin.Lift.instance_for`). *)
let shallow_ty (sty: Ast.sty): T.term = `PSSB.shallow (`#sty)

(* Like `shallow_ty`, but with the `has_stream` typeclass instance
   provided explicitly as `inst`. Built as raw `Tv_App` so no implicit
   uvar is created — important when the instance is a local binder
   whose scope F* would otherwise lose track of. *)
let shallow_ty_with_inst (sty: Ast.sty) (inst: T.term): T.term =
  let shallow_fv: T.term =
    T.pack (T.Tv_FVar (T.pack_fv ["Pipit"; "Prim"; "HasStream"; "shallow"])) in
  let applied: T.term = T.pack (T.Tv_App shallow_fv (sty, T.Q_Explicit)) in
  T.pack (T.Tv_App applied (inst, T.Q_Implicit))

(* Build a `shallow sty` term using `env.inst_for` when possible. *)
let shallow_ty_for_env (env: lower_env) (sty: Ast.sty): T.Tac T.term =
  match env.inst_for sty with
  | Some inst -> shallow_ty_with_inst sty inst
  | None      -> shallow_ty sty

let exp_XVal  (v: T.term): T.term =
  `(PXB.XBase #PPS.table (PXB.XVal #PPS.table (`#v)))

let exp_XBVar (i: T.term): T.term =
  `(PXB.XBase #PPS.table (PXB.XBVar #PPS.table (`#i)))

let exp_XLet  (sty: T.term) (def: T.term) (body: T.term): T.term =
  `(PXB.XLet #PPS.table (`#sty) (`#def) (`#body))

let exp_XMu   (body: T.term): T.term =
  `(PXB.XMu #PPS.table (`#body))

let exp_XFby  (v: T.term) (e: T.term): T.term =
  `(PXB.XFby #PPS.table (`#v) (`#e))

let exp_XCheck (e: T.term): T.term =
  `(PXB.XCheck #PPS.table PM.PSUnknown (`#e))

(* Compute the FQN of a lifted source binding's `__core_*` sigelt by
   replacing the last segment `nm` with `nm ^ "_core"`. Mirrors
   `Pipit.Plugin.Lift.env_core_nm`. *)
let core_fqn_of (src: Ast.fqn): T.Tac Ast.fqn =
  match L.rev src with
  | [] -> T.fail "Pipit.Source.Ast.Lower: empty FQN for lifted call"
  | nm :: rest -> L.rev ((nm ^ "_core") :: rest)

(* Build a typed F* list term `[e1; e2; ...] : list elem_ty`. The
   element type is needed so that nil/cons disambiguate; here we use it
   to build a `list shallow_type` for cexp contexts. *)
let rec list_term (elem_ty: T.term) (xs: list T.term): T.term =
  match xs with
  | [] -> `([] <: list (`#elem_ty))
  | x :: rest ->
    let tail = list_term elem_ty rest in
    `((`#x) :: (`#tail))

(* Shallow context (innermost first) for a list of source types in
   innermost-first order. *)
let context_term (env: lower_env) (sty_innermost_first: list Ast.sty): T.Tac T.term =
  let elem_ty: T.term = `Pipit.Prim.Shallow.shallow_type in
  list_term elem_ty (T.map (shallow_ty_for_env env) sty_innermost_first)

(* Wrap a body with a chain of XLets. `defs_innermost_first` lists the
   (sty, def) pairs in the order they were bound, innermost first
   (i.e. `[(t_n, a_n); ...; (t_1, a_1)]`), so the outermost XLet binds
   the first source argument and the innermost binds the last. *)
let rec wrap_xlets (env: lower_env) (defs_innermost_first: list (Ast.sty & T.term)) (body: T.term): T.Tac T.term =
  match defs_innermost_first with
  | [] -> body
  | (sty, def) :: rest ->
    let sh = shallow_ty_for_env env sty in
    let inner = exp_XLet sh def body in
    wrap_xlets env rest inner

(* Build a `funty shallow_type` term from argument and return source
   types: `FTFun a1 (FTFun a2 ... (FTVal r)) ...`. *)
let rec funty_of (env: lower_env) (arg_tys: list Ast.sty) (ret_ty: Ast.sty): T.Tac T.term =
  match arg_tys with
  | [] -> let r = shallow_ty_for_env env ret_ty in `(PPT.FTVal (`#r))
  | a :: rest ->
    let tail = funty_of env rest ret_ty in
    let sh = shallow_ty_for_env env a in
    `(PPT.FTFun (`#sh) (`#tail))

(* Build a `PPS.prim` record: `PPS.mkPrim id ft fn`. The `id` is wrapped
   as `Some s` / `None`. *)
let shallow_prim (env: lower_env) (id: option Ast.name) (arg_tys: list Ast.sty) (ret_ty: Ast.sty) (fn: T.term): T.Tac T.term =
  let id_tm: T.term =
    match id with
    | Some s -> `(Some (`#(T.pack (T.Tv_Const (T.C_String s)))))
    | None   -> `None
  in
  let ft_tm = funty_of env arg_tys ret_ty in
  `(PPS.mkPrim (`#id_tm) (`#ft_tm) (`#fn))

let exp_XPrim (p_tm: T.term): T.term =
  `(PXB.XPrim #PPS.table (`#p_tm))

let exp_XApp  (f: T.term) (a: T.term): T.term =
  `(PXB.XApp #PPS.table (`#f) (`#a))

let exp_XApps (e: T.term): T.term =
  `(PXB.XApps #PPS.table (`#e))

let int_const (i: int): T.term =
  T.pack (T.Tv_Const (T.C_Int i))

(* Allocate a fresh named variable of the given F* type and pretty name. *)
let fresh_nv (ppname: string) (ty: T.term): T.Tac T.namedv =
  { uniq = T.fresh (); sort = T.seal ty; ppname = R.as_ppname ppname }

(*** ALetMatch desugaring helpers ***)

(* Walk an [Ast.pat] (built by [Pipit.Source.Ast.Reflect.pat_of_fstar])
   and turn it into a chain of stream [Ast.ALet]s wrapping [body].
   Each leaf [PVar] becomes one [ALet] whose RHS is the appropriate
   projector application on [parent_nm]; nested [PCon] sub-patterns
   introduce an intermediate `_dst#N` name and recurse. [PWild]
   contributes no binding.

   Projector typechecking uses [T.top_env ()]; this is sufficient for
   destructure whose scrutinee type is ground at the splice site
   (tuples / records over concrete types — every test we have today).
   Polymorphic destructure (e.g. a `match` on `stream (a * b)` inside a
   `#a:eqtype -> #b:eqtype -> ...` source binding) would need the
   local type binders in scope; that would require threading a tactic
   env through [lower_env]. Deferred. *)

let rec pat_size (p: Ast.pat): nat =
  match p with
  | Ast.PCon _ subs -> 1 + pats_size subs
  | _ -> 1

and pats_size (ps: list Ast.pat): nat =
  match ps with
  | [] -> 0
  | p :: rest -> 1 + pat_size p + pats_size rest

(* Compute the FQN of F*'s auto-generated projector for a constructor's
   explicit field: replace the last segment `Ctor` of [ctor_fqn] with
   `__proj__Ctor__item__field`. *)
let projector_fqn (ctor_fqn: Ast.fqn) (field: Ast.name): T.Tac Ast.fqn =
  match L.rev ctor_fqn with
  | [] -> T.fail "Pipit.Source.Ast.Lower: empty constructor FQN"
  | ctor_nm :: rest_rev ->
    let proj_nm = "__proj__" ^ ctor_nm ^ "__item__" ^ field in
    L.rev (proj_nm :: rest_rev)

(* Explicit-binder ppnames of a data constructor, in declaration order.
   Used to compute projector FQNs (which suffix the field's ppname). *)
let ctor_field_names (env: T.env) (ctor_fv: T.fv): T.Tac (list Ast.name) =
  let ctor_tm = T.pack (T.Tv_FVar ctor_fv) in
  let ctor_ty = T.tc env ctor_tm in
  let (bs, _) = T.collect_arr_bs ctor_ty in
  let explicit_bs =
    L.filter (fun (b: T.binder) -> R.Q_Explicit? b.qual) bs
  in
  T.map (fun (b: T.binder) -> T.unseal b.ppname) explicit_bs

(* Recover the implicit type arguments threaded through a scrutinee's
   type. For [tuple2 int int] the head is the type constructor and the
   args are [int; int]; we re-tag as implicit so they instantiate the
   projector's [#a -> #b -> ...] binders. *)
let scrut_type_implicits (scrut_ty: T.term): T.Tac (list T.argv) =
  let (_, ty_args) = T.collect_app scrut_ty in
  T.map (fun (a: T.argv) -> let (t, _) = a in (t, T.Q_Implicit)) ty_args

(* Build an [Ast.prim] for a projector pre-applied to scrutinee type
   implicits. Mirrors [Pipit.Source.Ast.Reflect.of_prim_fv_applied]. *)
let mk_proj_prim (env: T.env) (proj_fqn: Ast.fqn) (implicits: list T.argv): T.Tac Ast.prim =
  let proj_fv = T.pack_fv proj_fqn in
  let proj_tm = T.pack (T.Tv_FVar proj_fv) in
  let proj_fn =
    match implicits with
    | [] -> proj_tm
    | _  -> T.mk_app proj_tm implicits
  in
  let ty        = T.tc env proj_fn in
  let (args, c) = T.collect_arr ty in
  let res_ty    = PTB.returns_of_comp c in
  {
    Ast.prim_id      = Some (R.implode_qn proj_fqn);
    Ast.prim_arg_tys = args;
    Ast.prim_ret_ty  = res_ty;
    Ast.prim_fn      = proj_fn;
  }

(* Desugar an [Ast.pat] against a parent named-binder [parent_nm] of
   type [parent_sty], producing an [Ast.ast] equivalent to the
   irrefutable destructure wrapped around [body]. *)
let rec pat_to_alet_chain (rng: R.range) (pat: Ast.pat)
                          (parent_nm: Ast.name) (parent_sty: Ast.sty)
                          (body: Ast.ast)
    : T.Tac Ast.ast
      (decreases (pat_size pat))
=
  match pat with
  | Ast.PWild -> body

  | Ast.PVar nm field_sty mode ->
    (* The whole parent value is bound to nm. *)
    let def = Ast.AVar rng parent_nm mode in
    Ast.ALet rng nm mode field_sty def body

  | Ast.PCon ctor_fqn sub_pats ->
    let env = T.top_env () in
    let ctor_fv = T.pack_fv ctor_fqn in
    let field_names = ctor_field_names env ctor_fv in
    (if L.length field_names <> L.length sub_pats then
      T.fail "Pipit.Source.Ast.Lower: pat arity mismatch (sub_pats vs ctor fields)"
     else ());
    let implicits = scrut_type_implicits parent_sty in
    pat_to_alet_chain_subs rng ctor_fqn field_names sub_pats implicits parent_nm body

and pat_to_alet_chain_subs (rng: R.range) (ctor_fqn: Ast.fqn)
                           (fields: list Ast.name) (subs: list Ast.pat)
                           (implicits: list T.argv) (parent_nm: Ast.name)
                           (body: Ast.ast)
    : T.Tac Ast.ast
      (decreases (pats_size subs))
=
  match fields, subs with
  | [], [] -> body
  | f :: fs, p :: ps ->
    (* Build the let chain for the remaining fields first; this field's
       binding is then placed OUTSIDE that, matching the source order. *)
    let rest = pat_to_alet_chain_subs rng ctor_fqn fs ps implicits parent_nm body in
    (match p with
     | Ast.PWild -> rest
     | Ast.PVar nm field_sty mode ->
       let env = T.top_env () in
       let proj_fqn = projector_fqn ctor_fqn f in
       let proj_prim = mk_proj_prim env proj_fqn implicits in
       let parent_ref = Ast.AVar rng parent_nm PPI.Stream in
       let proj_def: Ast.ast = Ast.APrim rng Ast.AppPureStream proj_prim [parent_ref] in
       Ast.ALet rng nm mode field_sty proj_def rest
     | Ast.PCon _ _ ->
       (* Nested constructor: bind an intermediate name to the projector
          application, then recurse on the nested pat. *)
       let env = T.top_env () in
       let proj_fqn = projector_fqn ctor_fqn f in
       let proj_prim = mk_proj_prim env proj_fqn implicits in
       let mid_nm = "_dst#" ^ string_of_int (T.fresh ()) in
       let mid_ty = proj_prim.Ast.prim_ret_ty in
       let parent_ref = Ast.AVar rng parent_nm PPI.Stream in
       let proj_def: Ast.ast = Ast.APrim rng Ast.AppPureStream proj_prim [parent_ref] in
       let nested = pat_to_alet_chain rng p mid_nm mid_ty rest in
       Ast.ALet rng mid_nm PPI.Stream mid_ty proj_def nested)
  | _, _ ->
    T.fail "Pipit.Source.Ast.Lower: pat sub arity mismatch (impossible)"

(*** AMatch (static multi-arm) desugaring helpers ***)

(* Termination measures for walking a [T.pattern] when pushing static
   binders for the arms of an [AMatch AppPureConst]. Parallel to the
   measures in [Pipit.Source.Ast.Reflect] but separately named so they
   don't shadow the [pat_size] on [Ast.pat] above. *)
let rec tpat_size (p: T.pattern): nat =
  match p with
  | T.Pat_Cons pc -> 1 + tpat_bool_subpats_size pc.subpats
  | _ -> 1

and tpat_bool_subpats_size (ss: list (T.pattern & bool)): nat =
  match ss with
  | [] -> 0
  | (p, _) :: rest -> 1 + tpat_size p + tpat_bool_subpats_size rest

(* Walk a [T.pattern] and push each leaf [Pat_Var] as a STATIC binder
   into [env], in pattern walk order (explicit subpats only). The
   pushed namedv is the pattern variable's original [bv.v] (preserving
   the uniq), and the binder name is computed using Reflect's
   convention ([ppname ^ "#" ^ string_of_int uniq]) so that the lifted
   body's name-based [AVar] lookups resolve to the namedv we just
   pushed. The arm's [T.pattern] can then be re-emitted verbatim
   under [Tv_Match] and F* will bind the pattern's bvs to occurrences
   of the same namedv in the lowered body. *)
let rec push_static_pat_binders (pat: T.pattern) (env: lower_env)
    : T.Tac lower_env
      (decreases (tpat_size pat))
=
  match pat with
  | T.Pat_Var pv ->
    let nv: T.namedv = pv.v in
    let nm: Ast.name = T.unseal nv.ppname ^ "#" ^ string_of_int nv.uniq in
    let sty: Ast.sty = T.unseal pv.sort in
    let b: binder = { b_name = nm; b_sty = sty; b_kind = BStatic nv } in
    env_push b env

  | T.Pat_Cons pc ->
    push_static_pat_binders_subs pc.subpats env

  | _ ->
    env

and push_static_pat_binders_subs (ss: list (T.pattern & bool)) (env: lower_env)
    : T.Tac lower_env
      (decreases (tpat_bool_subpats_size ss))
=
  match ss with
  | [] -> env
  | (_, true)  :: rest ->
    (* Implicit subpats — these correspond to elided type/dot
       arguments and don't introduce binders; skip them, matching the
       walk order used by [pat_of_fstar] in Reflect. *)
    push_static_pat_binders_subs rest env
  | (p, false) :: rest ->
    let env' = push_static_pat_binders p env in
    push_static_pat_binders_subs rest env'

(*** Entry points ***)

val lower_stream (env: lower_env) (a: Ast.ast): T.Tac T.term

val lower_static (env: lower_env) (a: Ast.ast): T.Tac T.term

let rec lower_stream env a =
  match a with
  | Ast.ALit _r lit ->
    exp_XVal lit.Ast.lit_tm

  | Ast.AVar _r n m ->
    (match m with
     | PPI.Stream ->
       (match env_bvar_index n env.binders with
        | Some i -> exp_XBVar (int_const i)
        | None -> T.fail ("Pipit.Source.Ast.Lower: stream variable not in scope: " ^ n))
     | PPI.Static ->
       (* Static values are lifted into stream context via XVal. *)
       let v_tm = lower_static env a in
       exp_XVal v_tm
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: unexpected functional mode on AVar: " ^ n))

  | Ast.APrim _r am p args ->
    (match am with
     | Ast.AppPureStream ->
       (* XApps (XApp (... (XApp (XPrim p) a1) ...) an) *)
       let prim_tm  = shallow_prim env p.Ast.prim_id p.Ast.prim_arg_tys p.Ast.prim_ret_ty p.Ast.prim_fn in
       let head     = exp_XPrim prim_tm in
       let arg_tms  = T.map (lower_stream env) args in
       let applied  = L.fold_left exp_XApp head arg_tms in
       exp_XApps applied
     | Ast.AppPureConst ->
       (* Static-only application; lift the resulting value into stream
          context via XVal. *)
       let v_tm = lower_static env a in
       exp_XVal v_tm)

  | Ast.ACallStream _r br args ->
    (* Lower a call to another `#lang-pipit` binding `f a1 .. an`. The
       callee's `f_core` may be polymorphic over Static F* params
       (real `Tv_Abs` binders) followed by a cexp expression in its
       Stream params: `f_core : s1 -> ... -> sk -> exp t [tn; ...; t1] r`
       (innermost-first context, stream params only). We:
         1. Walk `br.br_mode` to split args into static (lowered to F*
            terms and applied via `Tv_App`) and stream (kept for the
            cexp `XLet`/`weaken` chain).
         2. Build the cexp ctx and weaken/XLet chain from the stream
            args only, in source order. Static args are out of band
            and don't shift caller de Bruijn indices. *)
    let arg_tys = br.Ast.br_arg_tys in
    let n_src = L.length arg_tys in
    let n_arg = L.length args in
    if n_src <> n_arg then
      T.fail ("Pipit.Source.Ast.Lower: ACallStream arg count mismatch for "
              ^ R.implode_qn br.Ast.br_fqn ^ ": signature has "
              ^ string_of_int n_src ^ " explicit params, call has "
              ^ string_of_int n_arg ^ " args")
    else
    (* Split args into (static asts in source order, (stream ast, sty)
       pairs in source order) by peeling one EXPLICIT `ModeFun` layer
       per arg from `br.br_mode`. `br_mode` contains one layer per
       source binder (including implicits / instance binders), so we
       drop leading `ModeFun ... explicit=false ...` layers first.
       Defensive default: treat as Stream if `br_mode` is exhausted. *)
    let rec skip_implicits (m: PPI.mode): PPI.mode =
      match m with
      | PPI.ModeFun _ false rm -> skip_implicits rm
      | _ -> m
    in
    let rec partition_args (m: PPI.mode) (args: list Ast.ast) (tys: list Ast.sty)
      : T.Tac (list Ast.ast & list (Ast.ast & Ast.sty))
    =
      match args, tys with
      | [], [] -> ([], [])
      | a :: ras, t :: rts ->
        let m = skip_implicits m in
        let (arg_mode, rm): PPI.mode & PPI.mode = match m with
          | PPI.ModeFun am _ rm -> (am, rm)
          | _ -> (PPI.Stream, m)
        in
        let (ss, sts) = partition_args rm ras rts in
        (match arg_mode with
         | PPI.Static -> (a :: ss, sts)
         | _ -> (ss, (a, t) :: sts))
      | _, _ ->
        T.fail "Pipit.Source.Ast.Lower: ACallStream arg/ty mismatch (impossible)"
    in
    let (static_args, stream_args_tys) = partition_args br.Ast.br_mode args arg_tys in
    let core_fqn = core_fqn_of br.Ast.br_fqn in
    let core_fv_tm = T.pack (T.Tv_FVar (T.pack_fv core_fqn)) in
    (* Pre-apply the call-site implicits to the callee's `__core_*`
       reference so polymorphic callees become monomorphic at this
       call site. For ground callees `br_implicits` is empty and this
       is a no-op. *)
    let core_fv_tm =
      match br.Ast.br_implicits with
      | [] -> core_fv_tm
      | _  -> T.mk_app core_fv_tm br.Ast.br_implicits
    in
    (* Apply each static arg as an F* `Tv_App` (explicit) to the core
       reference, in source order (outermost-static first). *)
    let core_fv_tm =
      T.fold_left
        (fun (acc: T.term) (a: Ast.ast) ->
          let v_tm = lower_static env a in
          T.pack (T.Tv_App acc (v_tm, T.Q_Explicit)))
        core_fv_tm
        static_args
    in
    let stream_tys = L.map snd stream_args_tys in
    let stream_args = L.map fst stream_args_tys in
    (* Caller-side stream context (innermost first). *)
    let caller_stream_ctx = stream_ctx_of_binders env.binders in
    (* Callee context (innermost first) = reverse of stream param tys. *)
    let callee_ctx = L.rev stream_tys in
    let callee_ctx_tm = context_term env callee_ctx in
    let caller_ctx_tm = context_term env caller_stream_ctx in
    (* The weakened core sits at the bottom of the XLet chain, in
       context `callee_ctx ++ caller_stream_ctx`. *)
    let weakened = `(PXB.weaken #PPS.table #(`#callee_ctx_tm) (`#caller_ctx_tm) (`#core_fv_tm)) in
    (* Lower each stream argument in env extended with dummy stream
       binders for preceding args (innermost first). *)
    let rec lower_args (acc_dummies_innermost_first: list binder)
                       (defs_innermost_first: list (Ast.sty & T.term))
                       (rem_tys: list Ast.sty)
                       (rem_args: list Ast.ast)
                       : T.Tac (list (Ast.sty & T.term)) =
      match rem_tys, rem_args with
      | [], [] -> defs_innermost_first
      | sty :: rest_tys, a :: rest_args ->
        let cur_env: lower_env = { env with binders = L.append acc_dummies_innermost_first env.binders } in
        let a_tm = lower_stream cur_env a in
        let dummy_name = "__arg_dummy_" ^ string_of_int (T.fresh ()) in
        let dummy: binder = { b_name = dummy_name; b_sty = sty; b_kind = BStream } in
        lower_args (dummy :: acc_dummies_innermost_first)
                   ((sty, a_tm) :: defs_innermost_first)
                   rest_tys rest_args
      | _, _ ->
        T.fail "Pipit.Source.Ast.Lower: ACallStream arg count mismatch (impossible)"
    in
    let defs_innermost_first = lower_args [] [] stream_tys stream_args in
    wrap_xlets env defs_innermost_first weakened

  | Ast.AFby _r lit e ->
    let e_tm = lower_stream env e in
    exp_XFby lit.Ast.lit_tm e_tm

  | Ast.ALet _r n m sty def body ->
    (match m with
     | PPI.Stream ->
       let def_tm = lower_stream env def in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStream } in
       let env' = env_push b env in
       let body_tm = lower_stream env' body in
       exp_XLet (shallow_ty_for_env env sty) def_tm body_tm
     | PPI.Static ->
       (* Encoded as `(fun (n: sty) -> body) def` so that F* substitutes
          `def` for `n` during normalisation. *)
       let def_tm = lower_static env def in
       let nv = fresh_nv n sty in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStatic nv } in
       let env' = env_push b env in
       let body_tm = lower_stream env' body in
       let abs_tm = T.pack (T.Tv_Abs (T.namedv_to_binder nv sty) body_tm) in
       T.mk_app abs_tm [(def_tm, T.Q_Explicit)]
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: ALet with functional mode is not supported: " ^ n))

  | Ast.AMu _r n sty body ->
    let b: binder = { b_name = n; b_sty = sty; b_kind = BStream } in
    let env' = env_push b env in
    let body_tm = lower_stream env' body in
    exp_XMu body_tm

  | Ast.ALetMatch r pat scrut_sty scrut_ast body_ast ->
    (* Bind the scrutinee to a fresh name and desugar [pat] into a
       chain of stream ALets over that name; recursively lower the
       resulting AST. The desugaring (projector applications,
       intermediate `_dst#N` names for nested ctor patterns) is in
       [pat_to_alet_chain]. *)
    let scrut_nm: Ast.name = "_scrut#" ^ string_of_int (T.fresh ()) in
    let desugared_body = pat_to_alet_chain r pat scrut_nm scrut_sty body_ast in
    let with_scrut: Ast.ast =
      Ast.ALet r scrut_nm PPI.Stream scrut_sty scrut_ast desugared_body
    in
    lower_stream env with_scrut

  | Ast.AMatch _r am scrut_ast _scrut_sty arms ->
    (* Static-scrutinee multi-arm match. The scrutinee lowers to a
       static F* term; each arm body lowers to a stream `exp` after
       pushing the pattern's binders as STATIC into the env. We emit
       a plain F* `Tv_Match` whose branches return `exp` values --
       at each call site the scrut resolves to a concrete
       constructor and F* normalises the match away. *)
    (match am with
     | Ast.AppPureConst ->
       let scrut_tm = lower_static env scrut_ast in
       let lowered_arms =
         T.map (fun ((pat, body): T.pattern & Ast.ast) ->
           let env_arm = push_static_pat_binders pat env in
           let body_tm = lower_stream env_arm body in
           (pat, body_tm)
         ) arms
       in
       T.pack (T.Tv_Match scrut_tm None lowered_arms)
     | Ast.AppPureStream ->
       T.fail "Pipit.Source.Ast.Lower: AMatch on stream scrutinee is not yet supported")

  | Ast.ALetrec _r bs cont ->
    (* v0: support a single static recursive binding only. The legacy
       `Pipit.Plugin.Lift` already treats every `Tv_Let true` as static
       and doesn't recurse into its body, so this is no less expressive.
       Stream-typed recursion belongs to `AMu`; mutual recursion would
       need a tuple encoding and is deferred. *)
    (match bs with
     | [(n, sty, def_ast)] ->
       let nv = fresh_nv n sty in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStatic nv } in
       let env' = env_push b env in
       let def_tm  = lower_static env' def_ast in
       let body_tm = lower_stream env' cont in
       T.pack (T.Tv_Let true [] (T.namedv_to_binder nv sty) def_tm body_tm)
     | [] ->
       T.fail "Pipit.Source.Ast.Lower: ALetrec with no bindings"
     | _ ->
       T.fail "Pipit.Source.Ast.Lower: ALetrec with mutual bindings is not yet supported (only single-binding rec is implemented)")

  | Ast.ACheck _r _olab e ->
    let e_tm = lower_stream env e in
    exp_XCheck e_tm

and lower_static env a =
  match a with
  | Ast.ALit _r lit -> lit.Ast.lit_tm

  | Ast.AVar _r n m ->
    (match m with
     | PPI.Static ->
       (match env_lookup n env.binders with
        | Some b ->
          (match b.b_kind with
           | BStatic nv -> T.pack (T.Tv_Var nv)
           | BStream ->
             T.fail ("Pipit.Source.Ast.Lower: stream variable used in static context: " ^ n))
        | None ->
          T.fail ("Pipit.Source.Ast.Lower: static variable not in scope: " ^ n))
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: non-static variable used in static context: " ^ n))

  | Ast.APrim _r am p args ->
    (match am with
     | Ast.AppPureConst ->
       (* Direct F* application. *)
       let arg_tms = T.map (fun a -> (lower_static env a, T.Q_Explicit)) args in
       T.mk_app p.Ast.prim_fn arg_tms
     | _ ->
       T.fail "Pipit.Source.Ast.Lower: APrim with stream app_mode used in static context")

  | Ast.ACallStream _r _br _args ->
    T.fail "Pipit.Source.Ast.Lower: ACallStream used in static context (stream-aware calls only valid in stream context)"

  | _ ->
    T.fail "Pipit.Source.Ast.Lower: static lowering only supports ALit, AVar, and APrim AppPureConst so far"

(* Top-level entry: lower an AST node as a stream/exp term. *)
let lower (env: lower_env) (a: Ast.ast): T.Tac T.term =
  lower_stream env a
