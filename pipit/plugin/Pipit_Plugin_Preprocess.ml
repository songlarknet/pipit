open Fstarcompiler
open FStar_Pervasives

module FCE  = FStarC_Compiler_Effect
module FPA  = FStarC_Parser_AST
module FPAU = FStarC_Parser_AST_Util
module FI   = FStarC_Ident
module FC   = FStarC_Const

let rec pat_is_strm_rec (p: FPA.pattern): bool =
  match p.pat with
  | PatWild _ | PatConst _ | PatVar _
  | PatName _
  | PatList _
  | PatTuple _
  | PatRecord _
  -> true
  | PatApp _ -> false
  | PatAscribed (p, _) -> pat_is_strm_rec p
  (* not sure about these *)
  | PatOp _ | PatVQuote _ | PatOr _ -> false

let rec tm_is_strm_rec (t: FPA.term): bool =
  match t.tm with
  | Abs _ -> false
  | Paren t -> tm_is_strm_rec t
  | _ -> true

let attr_cons m r attrs =
  let attr = Pipit_Plugin_Support.quote_mode_attr m r in
  Some (attr :: Option.value attrs ~default: [])

let rec mk_lets r binds body =
  match binds with
  | [] -> body
  | b :: binds ->
    FPA.mk_term (FPA.Let (FPA.LocalNoLetQualifier, [b], mk_lets r binds body)) r FPA.Expr

let rec mk_rec_snds t id0 index: FPA.term =
  let open FPA in
  if index = 0
  then { t with tm = Var id0 }
  else
    let x0 = mk_rec_snds t id0 (index - 1) in
    let snd = { t with tm = FPA.Name (FI.lid_of_str "snd")} in
    { t with tm = FPA.App (snd, x0, Nothing) }

let mk_rec_extract t id0 index: FPA.term =
  let x0 = mk_rec_snds t id0 index in
  let fst = { t with tm = FPA.Name (FI.lid_of_str "fst")} in
  { t with tm = FPA.App (fst, x0, Nothing) }


(* Collect ALL argument patterns from a top-level let pattern that are
   statically-typed (no `stream` type annotation), filtering out stream
   binders wherever they appear.  In F*'s surface syntax, top-level
   function arguments live in the LHS pattern as
     PatAscribed (PatApp (f, [arg1; arg2; ...]), ret_ty)
   rather than as Abs binders on the RHS body.

   Collecting ALL statics (not just a leading prefix) is necessary for
   mixed argument lists such as
     (inc: stream bool) (max: int)
   where the static `max` follows a stream binder.  The lifter always
   hoists static binders to the outermost positions of `_core` in
   source order, so filtering preserves the right application order.

   Must be called on the ORIGINAL pattern (before mode_of_pattern strips
   the `stream` annotations), because `stream` is the only marker
   distinguishing static from stream binders. *)
let rec static_pat_binders (p: FPA.pattern): FPA.pattern list =
  match p.pat with
  | FPA.PatAscribed (inner, _) -> static_pat_binders inner
  | FPA.PatApp (_, args) ->
    List.filter_map (fun arg ->
      let (m, _, _) = Pipit_Plugin_Support.mode_of_pattern arg in
      if Pipit_Plugin_Support.mode_any_stream m
      then None   (* stream binder: skip *)
      else Some arg
    ) args
  | _ -> []

(* Extract a `Var <id>` term from a simple binder pattern
   (`PatVar id` or `PatAscribed (PatVar id, ...)`).  Used to build the
   static-arg applications inside a parameterised `__check_<id>`. *)
let rec pat_var_term (range: FStarC_Range.range) (p: FPA.pattern): FPA.term =
  let level = FPA.Expr in
  match p.pat with
  | FPA.PatAscribed (inner, _) -> pat_var_term range inner
  | FPA.PatVar (id, _, _) ->
    { tm = FPA.Var (FI.lid_of_ids [id]); range; level }
  | _ ->
    Pipit_Plugin_Support.fatal range
      "proof_induct1: cannot extract variable from static binder pattern"

let rec pre_term (t: FPA.term): FPA.term =
  let go2 (t,i) = (pre_term t, i) in

  match t.tm with
  | Wild | Const _ | Uvar _
  | Var _ | Name _ | Projector _
  -> t
  | Op (i,ts) ->
    { t with tm = Op (i, List.map pre_term ts) }
  | Construct (l,ts) ->
    { t with tm = Construct (l, List.map go2 ts) }
  | Abs (ps, body) ->
    (* Strip `stream` from parameter type annotations (like pre_letbind does
       for let bindings). Attributes are not attached here since Abs parameters
       are not top-level; stream-mode is already captured by mode_of_pattern. *)
    let ps' = List.map (fun p ->
      let (_, _, p') = Pipit_Plugin_Support.mode_of_pattern p in
      p'
    ) ps in
    { t with tm = Abs (ps', pre_term body) }
  | Function (br,r) ->
    { t with tm = Function (List.map pre_branch br, r)}
  | App (a, b, c) ->
    { t with tm = App (pre_term a, pre_term b, c)}

  (* todo mut recs  *)
  | Let (LocalRec, [(attrs, (pat, def))], body)
    when pat_is_strm_rec pat && tm_is_strm_rec def
    ->
      let _, _, pat = Pipit_Plugin_Support.mode_of_pattern pat in
      let attrs = attr_cons Stream pat.prange attrs in
      let abs = {t with tm = FPA.Abs ([pat], def) } in
      let rec' = { t with tm = FPA.Name (Pipit_Plugin_Support.rec_lid t.range) } in
      let rec_app = { t with tm = FPA.App (rec', abs, FPA.Nothing) } in
      let letrec = { t with tm = FPA.Let (FPA.LocalNoLetQualifier, [(attrs, (pat, rec_app))], pre_term body) } in
      letrec

  | Let (LocalRec, binds, body)
    when List.for_all (fun (a,(p,t)) -> pat_is_strm_rec p && tm_is_strm_rec t) binds
    -> pre_letrecs t binds body


  | Let (q, tms, body) ->
    { t with tm = Let (q, List.map pre_letbind tms, pre_term body)}


  | Paren tm ->
    { t with tm = Paren (pre_term tm) }


  | LetOpen (l,e) ->
    { t with tm = LetOpen (l, pre_term e)}
  | LetOpenRecord (t1,t2,t3) ->
    { t with tm = LetOpenRecord (pre_term t1, pre_term t2, pre_term t3)}
  | Seq (e, e') ->
    { t with tm = Seq (pre_term e, pre_term e')}
  | Bind (i,e,e') ->
    { t with tm = Bind (i, pre_term e, pre_term e')}
  | If (p, op, ret, tru, fal) ->
    (* TODO descend into ret *)
    (* TODO add type ascriptions to ensure type is readily available *)
    { t with tm = If (pre_term p, op, ret, pre_term tru, pre_term fal)}
  | Match (scrut, op, ret, brs) ->
    (* TODO descend into ret *)
    (* TODO add type ascriptions to ensure type is readily available *)
    { t with tm = Match (pre_term scrut, op, ret, List.map pre_branch brs)}
  | Ascribed (e, ty, tac, is_eq) ->
    let m, ty = Pipit_Plugin_Support.mode_of_type ty in
    { t with tm = Ascribed (pre_term e, ty, Option.map pre_term tac, is_eq) }
  | Record (ot, lts) ->
    { t with tm = Record (Option.map pre_term ot, List.map (fun (l,t) -> (l, pre_term t)) lts)}
  | Project (e,l) ->
    { t with tm = Project (pre_term e, l) }
  | Discrim _ -> t
  | Attributes ts ->
    { t with tm = Attributes (List.map pre_term ts) }
  | ListLiteral ts ->
    { t with tm = ListLiteral (List.map pre_term ts) }
  | SeqLiteral ts ->
    { t with tm = SeqLiteral (List.map pre_term ts) }

  (* types - no need to descend? *)
  | Product (bs,e) -> t
  | Sum (lebt, e) -> t
  | Refine (b,e) -> t

  | LetOperator _
  | TryWith _
  | QForall _ | QExists _ | QuantOp _
  | Requires _ | Ensures _ | LexList _
  | WFOrder _ | Decreases _ | Labeled _
  | Antiquote _ | Quote _ | VQuote _
  | CalcProof _
  | IntroForall _ | IntroExists _ | IntroImplies _
  | IntroOr _ | IntroAnd _
  | ElimForall _ | ElimExists _ | ElimImplies _
  | ElimOr _ | ElimAnd _
    ->
    Pipit_Plugin_Support.fatal t.range ("preprocessor: expression not supported: " ^ FPA.term_to_string t)

  and pre_letbind ((attrs, (p, t)): FPA.term list option * (FPA.pattern * FPA.term)) =
    let t = pre_term t in
    let m, _x, p = Pipit_Plugin_Support.mode_of_pattern p in
    (attr_cons m p.prange attrs, (p, pre_term t))
  and pre_branch (p,tt,br) =
    let m, _x, p = Pipit_Plugin_Support.mode_of_pattern p in
    (* TODO where to put m attribute for stream mode? *)
    (p, Option.map pre_term tt, pre_term br)

  and pre_letrecs t binds body =
    let r = t.range in
    let id0  = FI.gen' "pipit_letrec" r in
    let pat0: FPA.pattern = { pat = FPA.PatVar (id0, None, []); prange = r } in
    let pats = List.map (fun (a,(p,t)) ->
      let (_m,_x,p) = Pipit_Plugin_Support.mode_of_pattern p in p) binds in
    let lid0 = FI.lid_of_ids [id0] in
    let exts = List.mapi (fun i _ -> mk_rec_extract t lid0 i) binds in
    let ext_binds = List.map2 (fun p e -> (None, (p, e))) pats exts in
    let attrs = attr_cons Stream r None in
    (* TODO subst in ext_binds *)
    let def_binds = List.map2 (fun p (_,(_,b)) -> (None, (p, b))) pats binds in
    let constr = List.fold_right (fun (_,(_,a)) b -> FPA.mkTuple [a; b] r) binds (FPA.unit_const r)  in
    let def = mk_lets r (ext_binds @ def_binds) constr in
    let abs: FPA.term = { t with tm = FPA.Abs ([pat0], def) } in
    let rec' = { t with tm = FPA.Name (Pipit_Plugin_Support.rec_lid r) } in
    let rec_app = { t with tm = FPA.App (rec', abs, FPA.Nothing) } in
    let rec_bind = (None, (pat0, rec_app)) in
    let let_binds = rec_bind :: ext_binds in
    let letrec = mk_lets r let_binds (pre_term body) in
    letrec


(* Look up the source identifier of a top-level let pattern. Returns a
  synthetic [error_pat_not_found] ident if the pattern shape is unexpected;
  callers should treat that as a hard error at a later stage. *)
let rec id_of_pat (p: FPA.pattern): FI.ident =
  let open FPA in
  match p.pat with
  | PatApp (p, _) -> id_of_pat p
  | PatVar (i, _, _) -> i
  | PatAscribed (p, _) -> id_of_pat p
  | _ -> FI.mk_ident ("error_pat_not_found", p.prange)


let mk_splice (pat: FPA.pattern) (mode: Pipit_Plugin_Support.mode): FPA.decl' =
  let open FPA in
  let range = pat.prange in
  let level = Expr in
  let id = id_of_pat pat in
  (* Use a deterministic but obviously-generated name so consumers (e.g.
    _check bindings) can temporarily refer to the spliced core expression.
    In the long term users should not need to mention this binding directly. *)
  let fresh = FI.mk_ident (FI.string_of_id id ^ "_core", range) in
  let mk_id_str i = { tm = Const (FC.Const_string (FI.string_of_id i, range)); range; level } in
  let tac =
    mkExplicitApp
    { tm = Var (Pipit_Plugin_Support.lift_tac_lid range); range; level }
    [mk_id_str id; mk_id_str fresh]
    range
  in
  let tac_abs = {
    tm = Abs ([{ pat = PatWild (None, []); prange = range }], tac);
    range; level
  } in
  Splice (false, [fresh], tac_abs)

(* Build a [%splice[has_stream_<id>] (fun () -> derive_has_stream "<id>")]
  decl for the tycon with short name [id]. The tactic itself does the
  arity / single-ctor validation, so we don't replicate it here. *)
let mk_derive_has_stream_splice
    (id: FI.ident)
    (drange: FStarC_Range.range)
    : FPA.decl
  =
  let open FPA in
  let range = drange in
  let level = Expr in
  let id_str = FI.string_of_id id in
  let inst_id = FI.mk_ident ("has_stream_" ^ id_str, range) in
  let id_const = { tm = Const (FC.Const_string (id_str, range)); range; level } in
  let tac =
    mkExplicitApp
      { tm = Var (Pipit_Plugin_Support.derive_has_stream_tac_lid range); range; level }
      [id_const]
      range
  in
  let tac_abs = {
    tm = Abs ([{ pat = PatWild (None, []); prange = range }], tac);
    range; level
  } in
  {
    d = Splice (false, [inst_id], tac_abs);
    drange;
    quals = [];
    attrs = [];
    interleaved = false;
  }

(* Build the synthesised `__check_<id>` declaration for `[@@proof_induct1]`.

  It expands to roughly:
    [@@core_of_source (`%<id>) <mode>]
    let __check_<id> =
      assert (induct1 (system_of_exp __core_<id>)) by (norm_full []);
      bless __core_<id>

  This is arity-polymorphic in the source function: `bless` and
  `system_of_exp` accept any cexp context, so the same shape works whether
  `<id>` has 1, 2, 3, ... stream arguments.

  If `expect_failure` is true, the synthesised check additionally carries
  `[@@expect_failure]` so the module typechecks only when the check fails.
  This is used by `[@@proof_induct1_expect_failure]` for negative tests.
*)
let mk_check_induct1_decl
    (pat: FPA.pattern)
    (mode: Pipit_Plugin_Support.mode)
    (static_pats: FPA.pattern list)
    (expect_failure: bool)
    (drange: FStarC_Range.range): FPA.decl =
  let open FPA in
  let range = pat.prange in
  let level = Expr in
  let id = id_of_pat pat in
  let core_id  = FI.mk_ident (FI.string_of_id id ^ "_core",  range) in
  let check_id = FI.mk_ident ("__check_" ^ FI.string_of_id id, range) in
  let core_var = { tm = Var (FI.lid_of_ids [core_id]); range; level } in
  (* Apply any leading static binders to core_var, producing e.g.
     `count_when_core max` from `count_when_core` and `[max_pat]`. *)
  let core_applied =
    List.fold_left (fun app p ->
      mkExplicitApp app [pat_var_term range p] range
    ) core_var static_pats
  in
  let mk_lid_var lid =
    { tm = Var (lid range); range; level }
  in
  let sys_expr   = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.system_of_exp_lid) [core_applied] range in
  let ind_expr   = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.induct1_lid)        [sys_expr] range in
  let nil_list   = { tm = ListLiteral []; range; level } in
  let norm_call  = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.norm_full_lid)      [nil_list] range in
  (* thunk2 expansion: fun _ -> (); norm_full [] *)
  let unit_const = { tm = Const FC.Const_unit; range; level } in
  let thunk_body = { tm = Seq (unit_const, norm_call); range; level } in
  let thunk_term = {
    tm = Abs ([{ pat = PatWild (None, []); prange = range }], thunk_body);
    range; level
  } in
  let assert_call = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.assert_by_tactic_lid) [ind_expr; thunk_term] range in
  let bless_call  = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.bless_lid)            [core_applied] range in
  let body = { tm = Seq (assert_call, bless_call); range; level } in
  (* If there are static prefix binders, wrap the body in an Abs so
     the emitted declaration reads:
       let __check_count_when (max: int) = assert ...; bless (count_when_core max)
     rather than a raw value that fails to elaborate at `system_of_exp`. *)
  let check_body = match static_pats with
    | [] -> body
    | _  -> { tm = Abs (static_pats, body); range; level }
  in
  let check_pat = { pat = PatVar (check_id, None, []); prange = range } in
  let let_decl = TopLevelLet (NoLetQualifier, [(check_pat, check_body)]) in
  let src_vquote = {
    tm = VQuote { tm = Var (FI.lid_of_ids [id]); range; level };
    range; level
  } in
  let mode_term = Pipit_Plugin_Support.quote_mode mode range in
  let attr = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.core_of_source_lid) [src_vquote; mode_term] range in
  (* `core_lifted` so `norm_full` unfolds the binding when callers'
     induction proofs walk into it. Source -> core dispatch in
     `Pipit.Source.Ast.Util.find_core_for_source` picks the most
     recently defined `core_of_source` candidate, so this binding
     (emitted *after* the `<id>_core` splice) wins automatically. *)
  let lifted_attr = mk_lid_var Pipit_Plugin_Support.core_lifted_lid in
  let attrs =
    if expect_failure
    then [attr; lifted_attr; mk_lid_var Pipit_Plugin_Support.expect_failure_lid]
    else [attr; lifted_attr]
  in
  {
    d = let_decl;
    drange;
    quals = [];
    attrs;
    interleaved = false;
  }

(* Build the synthesised `<id>_contract` declaration for
  `[@@proof_contract (\`%rely) (\`%guar)]` on a body.

  It expands to roughly:
    [@@core_of_source (`%<id>) <mode>; core_lifted]
    let <id>_contract =
      assert (induct1 (system_of_contract <rely>_core <guar>_core <id>_core))
        by (norm_full []);
      bless_contract <rely>_core <guar>_core <id>_core

  As with `mk_check_induct1_decl`, this is arity-polymorphic: the
  user-side rely / guar / body each carry their own `[@@source_mode]`
  and `lift_ast_tac1` splice; only the *assembly* lives here. The
  `<id>_contract` wrapper inherits all callers via the
  `find_core_for_source` dispatch (latest `core_of_source` wins), so
  source-level references to `<id>` are routed through the blessed
  contract.
*)
let mk_contract_decl
    (pat: FPA.pattern)
    (mode: Pipit_Plugin_Support.mode)
    (static_pats: FPA.pattern list)
    (rely: FI.ident)
    (guar: FI.ident)
    (drange: FStarC_Range.range): FPA.decl =
  let open FPA in
  let range = pat.prange in
  let level = Expr in
  let id = id_of_pat pat in
  let core_id      = FI.mk_ident (FI.string_of_id id   ^ "_core",     range) in
  let rely_core_id = FI.mk_ident (FI.string_of_id rely ^ "_core",     range) in
  let guar_core_id = FI.mk_ident (FI.string_of_id guar ^ "_core",     range) in
  let contract_id  = FI.mk_ident (FI.string_of_id id   ^ "_contract", range) in
  let mk_lid_var lid =
    { tm = Var (lid range); range; level }
  in
  let mk_local_var (i: FI.ident) =
    { tm = Var (FI.lid_of_ids [i]); range; level }
  in
  (* Apply any leading static binders to each core var, producing e.g.
     `rely_core cfg` / `guar_core cfg` / `body_core cfg`. *)
  let apply_static base =
    List.fold_left (fun app p ->
      mkExplicitApp app [pat_var_term range p] range
    ) base static_pats
  in
  let r_var = apply_static (mk_local_var rely_core_id) in
  let g_var = apply_static (mk_local_var guar_core_id) in
  let b_var = apply_static (mk_local_var core_id) in
  let sys_expr =
    mkExplicitApp (mk_lid_var Pipit_Plugin_Support.system_of_contract_lid)
      [r_var; g_var; b_var] range in
  let ind_expr =
    mkExplicitApp (mk_lid_var Pipit_Plugin_Support.induct1_lid) [sys_expr] range in
  let nil_list  = { tm = ListLiteral []; range; level } in
  let norm_call = mkExplicitApp (mk_lid_var Pipit_Plugin_Support.norm_full_lid) [nil_list] range in
  let unit_const = { tm = Const FC.Const_unit; range; level } in
  let thunk_body = { tm = Seq (unit_const, norm_call); range; level } in
  let thunk_term = {
    tm = Abs ([{ pat = PatWild (None, []); prange = range }], thunk_body);
    range; level
  } in
  let assert_call =
    mkExplicitApp (mk_lid_var Pipit_Plugin_Support.assert_by_tactic_lid)
      [ind_expr; thunk_term] range in
  let bless_call =
    mkExplicitApp (mk_lid_var Pipit_Plugin_Support.bless_contract_lid)
      [r_var; g_var; b_var] range in
  let body = { tm = Seq (assert_call, bless_call); range; level } in
  (* Same Abs-wrap as mk_check_induct1_decl: static prefix args become
     top-level parameters of <id>_contract. *)
  let contract_body = match static_pats with
    | [] -> body
    | _  -> { tm = Abs (static_pats, body); range; level }
  in
  let contract_pat = { pat = PatVar (contract_id, None, []); prange = range } in
  let let_decl = TopLevelLet (NoLetQualifier, [(contract_pat, contract_body)]) in
  let src_vquote = {
    tm = VQuote { tm = Var (FI.lid_of_ids [id]); range; level };
    range; level
  } in
  let mode_term = Pipit_Plugin_Support.quote_mode mode range in
  let cof_attr =
    mkExplicitApp (mk_lid_var Pipit_Plugin_Support.core_of_source_lid)
      [src_vquote; mode_term] range in
  let lifted_attr = mk_lid_var Pipit_Plugin_Support.core_lifted_lid in
  {
    d = let_decl;
    drange;
    quals = [];
    attrs = [cof_attr; lifted_attr];
    interleaved = false;
  }

(* ----- Stream-effect return-type desugar -----

   In a `#lang-pipit` module, a user can write

     let f (a: stream A) (b: stream B): Stream Ret
       (requires R) (ensures fun r -> G)
       = body

   as sugar for the three separate bindings expected by the existing
   `proof_contract` machinery:

     let f_rely (a: stream A) (b: stream B): stream bool = R
     let f_guar (a: stream A) (b: stream B) (r: stream Ret): stream bool = G
     [@@proof_contract (`%f_rely) (`%f_guar)]
     let f      (a: stream A) (b: stream B): Ret = body

   Only the top-level return type is sugared; uses of `Stream` anywhere
   else (binder positions, nested return types) are left alone and will
   be rejected by F* downstream. *)

let rec unparen (t: FPA.term): FPA.term =
  match t.tm with
  | FPA.Paren t -> unparen t
  | _ -> t

(* Collect a left-nested chain of applications, returning the head and
   the list of arguments in left-to-right order.  `Paren` wrappers are
   transparent. *)
let collect_app_left (t: FPA.term): FPA.term * (FPA.term * FPA.imp) list =
  let rec go (t: FPA.term) acc = match t.tm with
    | FPA.App (f, a, q) -> go f ((a, q) :: acc)
    | FPA.Paren t -> go t acc
    | _ -> (t, acc)
  in
  go t []

(* Recognise `Stream <ret> (requires R) (ensures fun r -> G)`.
   Returns Some (ret_ty, R, r_ident, G_body) on a well-formed contract,
   None when the head isn't `Stream` at all, and fails fatally for an
   ill-formed `Stream ...` expression. *)
let detect_stream_ret_ty (ty: FPA.term):
  (FPA.term * FPA.term * FI.ident * FPA.term) option =
  let open FPA in
  (* F* parses `Stream int (requires R) (ensures G)` as either a
     `Construct (Stream, [int; requires R; ensures G])` (capitalised
     head, like a data constructor) or a chain of `App`s.  Accept
     either shape. *)
  let (head_lid_opt, args) =
    match (unparen ty).tm with
    | Construct (lid, args) -> (Some lid, args)
    | _ ->
      let (head, args) = collect_app_left ty in
      (match (unparen head).tm with
       | Var lid -> (Some lid, args)
       | _ -> (None, args))
  in
  match head_lid_opt with
  | Some lid when FI.string_of_lid lid = "Stream" ->
    let args' = List.map (fun (a, _) -> unparen a) args in
    (match args' with
     | [ret; req; ens] ->
       let r_term = match req.tm with
         | Requires r -> r
         | _ -> Pipit_Plugin_Support.fatal req.range
             "Stream contract: second argument must be `(requires <bool>)`"
       in
       let g_term = match ens.tm with
         | Ensures g -> g
         | _ -> Pipit_Plugin_Support.fatal ens.range
             "Stream contract: third argument must be `(ensures fun <r> -> <bool>)`"
       in
       let rec id_of_simple_pat p = match p.pat with
         | PatVar (i, _, _) -> i
         | PatAscribed (p, _) -> id_of_simple_pat p
         | _ -> Pipit_Plugin_Support.fatal p.prange
             "Stream contract: `ensures` lambda must bind a single name"
       in
       let (r_id, g_body) = match (unparen g_term).tm with
         | Abs ([pat], body) -> (id_of_simple_pat pat, body)
         | _ -> Pipit_Plugin_Support.fatal g_term.range
             "Stream contract: `ensures` argument must be `fun <r> -> ...`"
       in
       Some (ret, r_term, r_id, g_body)
     | _ ->
       Pipit_Plugin_Support.fatal ty.range
         "Stream contract: expected `Stream <ret> (requires R) (ensures fun r -> G)`")
  | _ -> None

let mk_stream_ty (ty: FPA.term) (range: FStarC_Range.range): FPA.term =
  let open FPA in
  let level = Expr in
  let stream_var =
    { tm = Var (FI.lid_of_path ["stream"] range); range; level }
  in
  { tm = App (stream_var, ty, Nothing); range; level }

let mk_bool_ty (range: FStarC_Range.range): FPA.term =
  let open FPA in
  { tm = Var (FI.lid_of_path ["bool"] range); range; level = Expr }

(* If the body of a top-level let binds a `Stream <ret> (requires R)
   (ensures fun r -> G)` return type, rewrite it to plain `<ret>`, add a
   `proof_contract <f>_rely <f>_guar` attribute, and emit two extra
   top-level lets for `<f>_rely` and `<f>_guar`. *)
let desugar_stream_decl
    (pat: FPA.pattern)
    (orig_attrs: FPA.term list)
    (drange: FStarC_Range.range):
  (FPA.pattern * FPA.term list * FPA.decl list) option =
  let open FPA in
  match pat.pat with
  | PatAscribed ({ pat = PatApp (head_pat, arg_pats); prange = inner_range },
                 (ret_ty_form, None)) ->
    (match detect_stream_ret_ty ret_ty_form with
     | None -> None
     | Some (ret_ty, r_term, r_id, g_body) ->
       let f_id = id_of_pat head_pat in
       let f_range = FI.range_of_id f_id in
       let rely_id = FI.mk_ident (FI.string_of_id f_id ^ "_rely", f_range) in
       let guar_id = FI.mk_ident (FI.string_of_id f_id ^ "_guar", f_range) in
       let stream_bool_ty = mk_stream_ty (mk_bool_ty drange) drange in
       let stream_ret_ty  = mk_stream_ty ret_ty drange in
       let mk_pat_var (i: FI.ident): pattern =
         { pat = PatVar (i, None, []); prange = FI.range_of_id i }
       in
       let mk_ascribed (p: pattern) (ty: term): pattern =
         { pat = PatAscribed (p, (ty, None)); prange = p.prange }
       in
       let rely_pat =
         mk_ascribed
           { pat = PatApp (mk_pat_var rely_id, arg_pats);
             prange = inner_range }
           stream_bool_ty
       in
       let r_arg_pat = mk_ascribed (mk_pat_var r_id) stream_ret_ty in
       let guar_pat =
         mk_ascribed
           { pat = PatApp (mk_pat_var guar_id, arg_pats @ [r_arg_pat]);
             prange = inner_range }
           stream_bool_ty
       in
       let mk_decl (p: pattern) (t: term): FPA.decl = {
         d = TopLevelLet (NoLetQualifier, [(p, t)]);
         drange;
         quals = [];
         attrs = [];
         interleaved = false;
       } in
       let rely_decl = mk_decl rely_pat r_term in
       let guar_decl = mk_decl guar_pat g_body in
       let new_body_pat = {
         pat = PatAscribed (
           { pat = PatApp (head_pat, arg_pats); prange = inner_range },
           (ret_ty, None));
         prange = pat.prange;
       } in
       let mk_vquote (i: FI.ident): term =
         let level = Expr in
         let inner = { tm = Var (FI.lid_of_ids [i]); range = drange; level } in
         { tm = VQuote inner; range = drange; level }
       in
       let pc_lid_var = {
         tm = Var (Pipit_Plugin_Support.proof_contract_lid drange);
         range = drange;
         level = Expr;
       } in
       let pc_attr =
         mkExplicitApp pc_lid_var [mk_vquote rely_id; mk_vquote guar_id] drange
       in
       Some (new_body_pat, orig_attrs @ [pc_attr], [rely_decl; guar_decl]))
  | _ -> None

let rec pre_decl (r: FStarC_Range.range) (d: FPA.decl) =
  match d.d with
  | TopLevelLet (NoLetQualifier, [pat, tm]) ->
    (match desugar_stream_decl pat d.attrs d.drange with
     | Some (new_pat, new_attrs, extra_decls) ->
       let body_d = {
         d with
         d = TopLevelLet (NoLetQualifier, [(new_pat, tm)]);
         attrs = new_attrs;
       } in
       let flatten dec = match pre_decl r dec with
         | Inl _ -> [dec]
         | Inr ds -> ds
       in
       let extras_out = List.concat_map flatten extra_decls in
       Inr (extras_out @ flatten body_d)
     | None ->
       let (pm, _x, pp) = Pipit_Plugin_Support.mode_of_pattern pat in
       if Pipit_Plugin_Support.mode_any_stream pm
       then begin
         let attr = Pipit_Plugin_Support.quote_mode_attr pm r in
         (* Collect static prefix binders from the ORIGINAL pattern before
            mode_of_pattern strips the `stream` annotations that distinguish
            static from stream binders. *)
         let static_pats = static_pat_binders pat in
         let tm = pre_term tm in
         (* prerr_endline (FPA.term_to_string tm); *)
         let splice = { d with d = mk_splice pat pm; attrs = []; quals = [] } in
         let parsed = Pipit_Plugin_Attributes.parse_attributes d.attrs in
         let src_attrs = Pipit_Plugin_Attributes.drop_plugin_attrs d.attrs in
         let proof_check =
           match parsed.proof with
           | Some Pipit_Plugin_Attributes.Induct1 ->
             [mk_check_induct1_decl pat pm static_pats parsed.proof_expect_failure r]
           | Some (Pipit_Plugin_Attributes.Contract { rely; guar }) ->
             [mk_contract_decl pat pm static_pats rely guar r]
           | None -> []
         in
         Inr ([{ d with d = TopLevelLet (NoLetQualifier, [pp, tm]); attrs = attr :: src_attrs };
               splice] @ proof_check)
       end
       else
         Inr [d])
    (* pre_let d.drange pat tm *)

  | TopLevelLet (Rec, ps) ->
    (* TODO: check that it is not a stream definition *)
    Inr [d]

  | Tycon (is_effect, is_class, tycons) ->
    let parsed = Pipit_Plugin_Attributes.parse_attributes d.attrs in
    if parsed.derive_has_stream
    then
      let src_attrs = Pipit_Plugin_Attributes.drop_plugin_attrs d.attrs in
      let ident_of_tycon (tc: FPA.tycon): FI.ident = match tc with
        | TyconAbstract (i, _, _)
        | TyconAbbrev   (i, _, _, _)
        | TyconRecord   (i, _, _, _, _)
        | TyconVariant  (i, _, _, _) -> i
      in
      let derived =
        List.map (fun tc ->
          mk_derive_has_stream_splice (ident_of_tycon tc) d.drange
        ) tycons
      in
      Inr ({ d with d = Tycon (is_effect, is_class, tycons); attrs = src_attrs }
           :: derived)
    else
      Inr [d]

  (* TODO: check that streams aren't used in bad positions? *)
  | _ -> Inr [d]


let rec pre_decls_acc (r: FStarC_Range.range) (ds: FPA.decl list) (acc: FPA.decl list):
  (FPAU.error_message, FPA.decl list) either =
  match ds with
  | [] -> Inr acc
  | d :: ds ->
    match pre_decl r d with
    | Inl err -> Inl err
    | Inr d -> pre_decls_acc r ds (acc @ d)

let pre_decls (r: FStarC_Range.range) (ds: FPA.decl list):
  (FPAU.error_message, FPA.decl list) either =
  pre_decls_acc r ds []