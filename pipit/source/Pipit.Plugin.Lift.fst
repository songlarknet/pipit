module Pipit.Plugin.Lift

open Pipit.Plugin.Interface

module Tac = FStar.Tactics.V2
module Ref = FStar.Reflection.V2

module PTB = Pipit.Tactics.Base

module Range = FStar.Range

module List = FStar.List.Tot

module Ast    = Pipit.Source.Ast
module AstR   = Pipit.Source.Ast.Reflect
module AstLow = Pipit.Source.Ast.Lower


// quote doesn't work with extraction (I think) so implement manually for modes
let rec quote_mode (m: mode): Tac.term =
  match m with
    | Stream -> `Stream
    | Static -> `Static
    | ModeFun m x m' ->
      let x = if x then `true else `false in
      `ModeFun (`#(quote_mode m)) (`#x) (`#(quote_mode m'))

// assuming Tac.unquote doesn't work for extraction?
let rec unquote_mode (tm: Tac.term): Tac.Tac mode =
  let err () = Tac.fail ("bad ModeFun: " ^ Tac.term_to_string tm) in
  match Tac.inspect tm with
  | Tac.Tv_FVar fv ->
    if Tac.inspect_fv fv = ["Pipit"; "Plugin"; "Interface"; "Stream"]
    then Stream
    else if Tac.inspect_fv fv = ["Pipit"; "Plugin"; "Interface"; "Static"]
    then Static
    else err ()
  | Tac.Tv_App hd (m', _) ->
    (match Tac.inspect hd with
    | Tac.Tv_App hd (x, _) ->
    (match Tac.inspect hd with
    | Tac.Tv_App hd (m, _) ->
    (match Tac.inspect hd with
    | Tac.Tv_FVar fv ->
    if Tac.inspect_fv fv = ["Pipit"; "Plugin"; "Interface"; "ModeFun"]
    then
    let x =
      match Tac.inspect x with
      | Tac.Tv_Const Tac.C_True -> true
      | Tac.Tv_Const Tac.C_False -> false
      | _ -> Tac.fail ("bad ModeFun: expected const bool, got " ^ Tac.term_to_string x)
    in
      ModeFun (unquote_mode m) x (unquote_mode m')
    else err ()
    | _ -> err ())
    | _ -> err ())
    | _ -> err ())
  | _ -> err ()

let debug_print (str: unit -> Tac.Tac string): Tac.Tac unit =
  if Tac.ext_getv "pipit:lift:debug" <> ""
  then (
    let ms = Tac.curms () in
    Tac.print ("[ppt-lift@" ^ string_of_int ms ^ "]: " ^ str ())
  )

let fail (#a: Type) (msg: string) (rng: Range.range) (ctx: list string): Tac.Tac a =
  let str0 = "Pipit: lift transform: failure at " ^ Tac.range_to_string rng ^ "\n  " ^ msg in
  let str = List.fold_left (fun str str' -> str ^ "\n    * " ^ str') str0 ctx in
  Tac.fail str

(* construct mapping from source to lifted core for given top-level binding *)
let env_lifted_mapping (tac_env: Tac.env) (lift_fv: Ref.fv): Tac.Tac (option (Ref.name & Ref.name & mode)) =
  let lift_nm = Tac.inspect_fv lift_fv in
  let lift_se = Tac.lookup_typ tac_env lift_nm in
  let rec go (attrs: list Tac.term): Tac.Tac (option (Ref.name & Ref.name & mode)) =
    match attrs with
    | [] -> None
    | hd :: tl ->
      let (hd,args) = Tac.collect_app hd in
      if PTB.term_check_fv hd (`%core_of_source)
      then (match args with
        | [(arg,_); (mode,_)] ->
          (match Tac.inspect arg with
          | Tac.Tv_Const (Ref.C_String nm) -> Some (lift_nm, Tac.explode_qn nm, unquote_mode mode)
          | _ -> fail
            ("cannot parse attribute " ^ Tac.term_to_string hd)
            (Tac.range_of_term arg)
            ["in binding " ^ Ref.implode_qn lift_nm])
        | _ -> go tl)
      else go tl
  in
  match lift_se with
  | Some se ->
    let attrs = Ref.sigelt_attrs se in
    go attrs
  | None -> None

let env_core_nm (nm: string): string =
  nm ^ "_core"

let rec mode_of_attrs (attrs: list Tac.term): Tac.Tac (option mode) =
  match attrs with
  | [] -> None
  | hd :: tl ->
    let (hd,args) = Tac.collect_app hd in
    if PTB.term_check_fv hd (`%source_mode)
    then (match args with
      | [(mode,_)] ->
        Some (unquote_mode mode)
      | _ -> fail
            ("cannot parse attribute " ^ Tac.term_to_string hd)
            (Tac.range_of_term hd)
            [])
    else mode_of_attrs tl

(* Resolve a `has_stream` instance for a stream type [sty] inside the
   spliced sigelt. For each Tv_Var [X] of kind [Type] in [sty], look
   up the corresponding pass-through instance binder via [inst_map],
   then build a `has_stream_tup2` chain for nested tuples.

   - If [sty] is `Tv_Var X` and [X] is in [inst_map]: return
     `Some (Tv_Var (binder_to_namedv b))` for the matching instance
     binder [b].
   - If [sty] is `tuple2 a b`: recurse on [a] and [b], wrap in
     `has_stream_tup2`. If both sides resolve to `None`, return
     `None` (let F* resolve via typeclass).
   - Otherwise: `None`, in which case the caller falls back to the
     quasi-quote `PSSB.shallow sty` (lets F* resolve the implicit at
     sigelt typecheck time — works for ground types like `int`, `bool`). *)
let rec resolve_inst
  (inst_map: list (nat & nat))
  (passthrough: list Tac.binder)
  (sty: Tac.term)
: Tac.Tac (option Tac.term) =
  let tup2_inst_fv: Tac.term =
    Tac.pack (Tac.Tv_FVar (Tac.pack_fv ["Pipit"; "Prim"; "HasStream"; "has_stream_tup2"])) in
  match Tac.inspect sty with
  | Tac.Tv_Var nv ->
    (match List.tryFind (fun (kv: nat & nat) -> fst kv = nv.uniq) inst_map with
     | Some (_, inst_uniq) ->
       (match List.tryFind (fun (b: Tac.binder) -> b.uniq = inst_uniq) passthrough with
        | Some b -> Some (Tac.pack (Tac.Tv_Var (Tac.binder_to_namedv b)))
        | None -> Tac.fail "resolve_inst: missing instance binder")
     | None -> None)
  | Tac.Tv_App outer (b_arg, _) ->
    (match Tac.inspect outer with
     | Tac.Tv_App inner (a_arg, _) ->
       (match Tac.inspect inner with
        | Tac.Tv_FVar fv ->
          if Tac.inspect_fv fv = ["FStar"; "Pervasives"; "Native"; "tuple2"]
             || Tac.inspect_fv fv = ["Prims"; "tuple2"]
          then
            let ia_opt = resolve_inst inst_map passthrough a_arg in
            let ib_opt = resolve_inst inst_map passthrough b_arg in
            (match ia_opt, ib_opt with
             | None, None -> None
             | _ ->
               let ia = (match ia_opt with
                         | Some t -> t
                         | None -> `(_ by (FStar.Tactics.Typeclasses.tcresolve ()))) in
               let ib = (match ib_opt with
                         | Some t -> t
                         | None -> `(_ by (FStar.Tactics.Typeclasses.tcresolve ()))) in
               let t0 = Tac.pack (Tac.Tv_App tup2_inst_fv (a_arg, Tac.Q_Implicit)) in
               let t1 = Tac.pack (Tac.Tv_App t0 (b_arg, Tac.Q_Implicit)) in
               let t2 = Tac.pack (Tac.Tv_App t1 (ia, Tac.Q_Implicit)) in
               Some (Tac.pack (Tac.Tv_App t2 (ib, Tac.Q_Implicit))))
          else None
        | Tac.Tv_UInst fv _ ->
          if Tac.inspect_fv fv = ["FStar"; "Pervasives"; "Native"; "tuple2"]
             || Tac.inspect_fv fv = ["Prims"; "tuple2"]
          then
            let ia_opt = resolve_inst inst_map passthrough a_arg in
            let ib_opt = resolve_inst inst_map passthrough b_arg in
            (match ia_opt, ib_opt with
             | None, None -> None
             | _ ->
               let ia = (match ia_opt with
                         | Some t -> t
                         | None -> `(_ by (FStar.Tactics.Typeclasses.tcresolve ()))) in
               let ib = (match ib_opt with
                         | Some t -> t
                         | None -> `(_ by (FStar.Tactics.Typeclasses.tcresolve ()))) in
               let t0 = Tac.pack (Tac.Tv_App tup2_inst_fv (a_arg, Tac.Q_Implicit)) in
               let t1 = Tac.pack (Tac.Tv_App t0 (b_arg, Tac.Q_Implicit)) in
               let t2 = Tac.pack (Tac.Tv_App t1 (ia, Tac.Q_Implicit)) in
               Some (Tac.pack (Tac.Tv_App t2 (ib, Tac.Q_Implicit))))
          else None
        | _ -> None)
     | _ -> None)
  | _ -> None

(* Parse the source binding into `Ast.ast`, then call
   `Pipit.Source.Ast.Lower.lower` to emit the core expression term. *)
let lift_ast_tac (nm_src nm_core: string) : Tac.Tac (list Tac.sigelt) =
  let tac_env = Tac.top_env () in
  let m = Tac.cur_module () in
  let nm_src_m = Ref.implode_qn List.(m @ [nm_src]) in
  let nm_core_m = Ref.implode_qn List.(m @ [nm_core]) in
  let nm_src_m_exp = Ref.explode_qn nm_src_m in
  let lb_src = PTB.lookup_lb_top tac_env nm_src_m_exp in
  let se_src = match Ref.lookup_typ tac_env nm_src_m_exp with
    | None -> Tac.fail "lift_ast_tac: impossible"
    | Some s -> s in
  let lb_mode = match mode_of_attrs (Ref.sigelt_attrs se_src) with
    | None -> Tac.fail "lift_ast_tac: expected source function to have source_mode annotation"
    | Some m -> m in
  (* Discover other `#lang-pipit` bindings already lifted in scope:
     each carries the `core_lifted` attribute and a `core_of_source`
     attribute pairing the source FQN with the binding's functional
     mode. `lift_ast_tac` consumes both, so calls to those bindings in
     `lb_src.lb_def` can be emitted as `ACallStream` rather than rejected
     as unknown primitives. *)
  let lifts_fvs = Ref.lookup_attr (`core_lifted) tac_env in
  let lifted_full = Tac.filter_map (env_lifted_mapping tac_env) lifts_fvs in
  let lifted_for_reflect: list (Ast.fqn & mode) =
    List.map (fun (_, src, m) -> (src, m)) lifted_full
  in
  let (passthrough, params, ret_ty, ast) =
    AstR.lift_top_body tac_env lifted_for_reflect lb_mode lb_src.lb_def in
  debug_print (fun () -> "lb_src.lb_typ: " ^ Tac.term_to_string lb_src.lb_typ);
  debug_print (fun () -> "lb_src.lb_def: " ^ Tac.term_to_string lb_src.lb_def);
  debug_print (fun () -> "passthrough count: " ^ string_of_int (List.Tot.length passthrough));
  debug_print (fun () -> "params      count: " ^ string_of_int (List.Tot.length params));
  debug_print (fun () -> "ret_ty: " ^ Tac.term_to_string ret_ty);
  (* A param is "static" if its declared mode (from `lb_mode`) is
     `PPI.Static`. Static params become real F* `Tv_Abs` binders
     around the spliced core sigelt (and BStatic in the lower_env so
     references in the body are emitted as `Tv_Var`). Everything else
     (Stream, ModeFun, etc.) stays as a cexp stream binding (BStream
     + an entry in the ctx list). *)
  let is_static_param (bob: Tac.binder & AstR.of_binder): bool =
    let (_, ob) = bob in
    ob.AstR.ob_mode = Static
  in
  (* Convert Reflect param binders to Lower binders. Reuse the
     original `T.binder`'s namedv for static params so `Tv_Var`
     references in the lowered body bind to the wrapping `Tv_Abs`. *)
  let to_lower (bob: Tac.binder & AstR.of_binder): AstLow.binder =
    let (b, ob) = bob in
    let kind: AstLow.binder_kind =
      if is_static_param bob
      then AstLow.BStatic (Tac.binder_to_namedv b)
      else AstLow.BStream
    in
    {
      AstLow.b_name = ob.AstR.ob_name;
      AstLow.b_sty  = ob.AstR.ob_sty;
      AstLow.b_kind = kind;
    } in
  (* `ret_ty` is computed in `lift_top_body` against the env that
     contains the pass-through + explicit binders, so any `Tv_Var`
     references use the SAME uniqs as the binders we use to wrap
     `lb_typ_core` below. Reading the return type out of
     `lb_src.lb_typ` would not work for polymorphic source bindings
     because F* may re-uniquify implicit type-param binders between
     `lb_typ` and `lb_def`, leaving the references unresolvable when
     the spliced sigelt's type is built. *)
  (* Build instance-resolver: for each pass-through `has_stream X`
     binder, map the Tv_Var uniq of `X` → instance binder uniq. *)
  let inst_map: list (nat & nat) =
    Tac.fold_left
      (fun (acc: list (nat & nat)) (b: Tac.binder) ->
        (* If `b.sort` is `has_stream (Tv_Var X)`, record (X.uniq, b.uniq). *)
        match Tac.inspect b.sort with
        | Tac.Tv_App head args_arg ->
          let (arg_tm, _) = args_arg in
          (match Tac.inspect head with
           | Tac.Tv_FVar fv ->
             if Tac.inspect_fv fv = ["Pipit"; "Prim"; "HasStream"; "has_stream"]
             then
               (match Tac.inspect arg_tm with
                | Tac.Tv_Var nv -> (nv.uniq, b.uniq) :: acc
                | _ -> acc)
             else acc
           | _ -> acc)
        | _ -> acc)
      []
      passthrough in
  debug_print (fun () ->
    "inst_map: [" ^
    List.fold_right (fun (kv: nat & nat) (acc: string) ->
      "(" ^ string_of_int (fst kv) ^ "->" ^ string_of_int (snd kv) ^ ") " ^ acc)
      inst_map "" ^ "]");
  let inst_for (sty: Tac.term): Tac.Tac (option Tac.term) =
    resolve_inst inst_map passthrough sty in
  (* `params` is outermost-first (source order). `lower_env.binders`
     and `ctx_list_tm` want innermost-first; reverse for those. The
     wrapping below (`Tv_Arrow` / `Tv_Abs`) wants outermost-first so
     it uses `params` directly via `List.fold_right`. *)
  let params_inner: list (Tac.binder & AstR.of_binder) = List.rev params in
  let stream_obs_inner: list AstR.of_binder =
    List.map snd (List.filter (fun bob -> not (is_static_param bob)) params_inner) in
  let static_binders_outer: list Tac.binder =
    List.map fst (List.filter is_static_param params) in
  debug_print (fun () -> "static_params count: " ^ string_of_int (List.Tot.length static_binders_outer));
  debug_print (fun () -> "stream_params count: " ^ string_of_int (List.Tot.length stream_obs_inner));
  let lower_env: AstLow.lower_env = {
    AstLow.binders = List.map to_lower params_inner;
    AstLow.inst_for = inst_for;
  } in
  let tm = AstLow.lower lower_env ast in
  (* Context list is built from the stream binders only (innermost
     first), matching the order in which `AstLow.lower` resolves
     de-Bruijn indices for `BStream` binders. Static binders are
     wrapped as F* `Tv_Abs` around the core sigelt instead.
     Built with raw `Tv_App` / `Tv_FVar` constructors (not quasi-quotes)
     so the implicit `has_stream` typeclass arguments inside each
     `shallow_ty` are not eagerly elaborated against the tactic env. *)
  let shallow_type_tm: Tac.term =
    Tac.pack (Tac.Tv_FVar (Tac.pack_fv ["Pipit"; "Prim"; "Shallow"; "shallow_type"])) in
  let cons_fv: Tac.term =
    Tac.pack (Tac.Tv_FVar (Tac.pack_fv ["Prims"; "Cons"])) in
  let nil_fv: Tac.term =
    Tac.pack (Tac.Tv_FVar (Tac.pack_fv ["Prims"; "Nil"])) in
  let nil_app: Tac.term =
    Tac.pack (Tac.Tv_App nil_fv (shallow_type_tm, Tac.Q_Implicit)) in
  let ctx_list_tm: Tac.term =
    Tac.fold_right
      (fun (b: AstR.of_binder) (acc: Tac.term) ->
        let sh = AstLow.shallow_ty_for_env lower_env b.AstR.ob_sty in
        let c0 = Tac.pack (Tac.Tv_App cons_fv (shallow_type_tm, Tac.Q_Implicit)) in
        let c1 = Tac.pack (Tac.Tv_App c0 (sh, Tac.Q_Explicit)) in
        Tac.pack (Tac.Tv_App c1 (acc, Tac.Q_Explicit)))
      stream_obs_inner
      nil_app in
  let lb_typ_core: Tac.term =
    let exp_fv = Tac.pack (Tac.Tv_FVar (Tac.pack_fv ["Pipit"; "Exp"; "Base"; "exp"])) in
    let table_fv = Tac.pack (Tac.Tv_FVar (Tac.pack_fv ["Pipit"; "Prim"; "Shallow"; "table"])) in
    let ret_sh = AstLow.shallow_ty_for_env lower_env ret_ty in
    let e0 = Tac.pack (Tac.Tv_App exp_fv (table_fv, Tac.Q_Explicit)) in
    let e1 = Tac.pack (Tac.Tv_App e0 (ctx_list_tm, Tac.Q_Explicit)) in
    Tac.pack (Tac.Tv_App e1 (ret_sh, Tac.Q_Explicit)) in
  (* Wrap both the type and the definition in pass-through binders (the
     polymorphic type / typeclass-instance params of the source binding)
     so the spliced sigelt is itself polymorphic. Inside the
     pass-through layer, wrap the explicit STATIC params as ordinary
     `Tv_Abs` / `Tv_Arrow` binders -- they're real F* args at call
     sites, not cexp stream binders. *)
  let lb_typ_static: Tac.term =
    List.fold_right
      (fun (b: Tac.binder) (acc: Tac.term) -> Tac.pack (Tac.Tv_Arrow b (Tac.C_Total acc)))
      static_binders_outer
      lb_typ_core in
  let lb_typ_tm: Tac.term =
    List.fold_right
      (fun (b: Tac.binder) (acc: Tac.term) -> Tac.pack (Tac.Tv_Arrow b (Tac.C_Total acc)))
      passthrough
      lb_typ_static in
  let lb_def_static: Tac.term =
    List.fold_right
      (fun (b: Tac.binder) (acc: Tac.term) -> Tac.pack (Tac.Tv_Abs b acc))
      static_binders_outer
      tm in
  let lb_def_tm: Tac.term =
    List.fold_right
      (fun (b: Tac.binder) (acc: Tac.term) -> Tac.pack (Tac.Tv_Abs b acc))
      passthrough
      lb_def_static in
  let lb_core: Tac.letbinding = {
    lb_fv  = Tac.pack_fv (Ref.explode_qn nm_core_m);
    lb_us  = [];
    lb_typ = lb_typ_tm;
    lb_def = lb_def_tm;
  } in
  debug_print (fun () -> "ast_core_sigelt name: " ^ nm_core_m);
  debug_print (fun () -> "ast_core_sigelt typ:  " ^ Tac.term_to_string lb_typ_tm);
  debug_print (fun () -> "ast_core_sigelt def:  " ^ Tac.term_to_string lb_def_tm);
  let rec count_arrows (t: Tac.term): Tac.Tac nat =
    match Tac.inspect t with
    | Tac.Tv_Arrow _ (Tac.C_Total t') -> 1 + count_arrows t'
    | _ -> 0 in
  let rec count_abs (t: Tac.term): Tac.Tac nat =
    match Tac.inspect t with
    | Tac.Tv_Abs _ t' -> 1 + count_abs t'
    | _ -> 0 in
  debug_print (fun () -> "typ arrows count: " ^ string_of_int (count_arrows lb_typ_tm));
  debug_print (fun () -> "def abs count: " ^ string_of_int (count_abs lb_def_tm));
  let sv: Tac.sigelt_view = Tac.Sg_Let {isrec=false; lbs=[lb_core]} in
  let se: Tac.sigelt = Tac.pack_sigelt sv in
  let se = Ref.set_sigelt_quals [Ref.NoExtract] se in
  let nm_src_const = Tac.pack (Tac.Tv_Const (Ref.C_String nm_src_m)) in
  let attrs = [
    `core_lifted;
    `core_of_source (`#nm_src_const) (`#(quote_mode lb_mode));
  ] in
  let se = Ref.set_sigelt_attrs attrs se in
  [se]

let lift_ast_tac1 (nm_src: string) : Tac.Tac (list Tac.sigelt) =
  lift_ast_tac nm_src (env_core_nm nm_src)
