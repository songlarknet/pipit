open FStar_Pervasives

module FCE  = FStar_Compiler_Effect
module FPA  = FStar_Parser_AST
module FPAU = FStar_Parser_AST_Util
module FI   = FStar_Ident
module FC   = FStar_Const

let rec pat_is_strm_rec (p: FPA.pattern): bool =
  match p.pat with
  | PatWild _ | PatConst _ | PatVar _
  | PatName _ | PatTvar _
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
    FPA.mk_term (FPA.Let (FPA.NoLetQualifier, [b], mk_lets r binds body)) r FPA.Expr

let rec mk_rec_snds t id0 index: FPA.term =
  let open FPA in
  if index = 0
  then { t with tm = Tvar id0 }
  else
    let x0 = mk_rec_snds t id0 (index - 1) in
    let snd = { t with tm = FPA.Name (FI.lid_of_str "snd")} in
    { t with tm = FPA.App (snd, x0, Nothing) }

let mk_rec_extract t id0 index: FPA.term =
  let x0 = mk_rec_snds t id0 index in
  let fst = { t with tm = FPA.Name (FI.lid_of_str "fst")} in
  { t with tm = FPA.App (fst, x0, Nothing) }


let rec pre_term (t: FPA.term): FPA.term =
  let go2 (t,i) = (pre_term t, i) in

  match t.tm with
  | Wild | Const _ | Tvar _ | Uvar _
  | Var _ | Name _ | Projector _
  -> t
  | Op (i,ts) ->
    { t with tm = Op (i, List.map pre_term ts) }
  | Construct (l,ts) ->
    { t with tm = Construct (l, List.map go2 ts) }
  | Abs (ps, body) ->
    (* TODO map mode_of_pat ps, but where to introduce attrs? *)
    { t with tm = Abs (ps, pre_term body) }
  | Function (br,r) ->
    { t with tm = Function (List.map pre_branch br, r)}
  | App (a, b, c) ->
    { t with tm = App (pre_term a, pre_term b, c)}

  (* todo mut recs  *)
  | Let (Rec, [(attrs, (pat, def))], body)
    when pat_is_strm_rec pat && tm_is_strm_rec def
    ->
      let _, _, pat = Pipit_Plugin_Support.mode_of_pattern pat in
      let attrs = attr_cons Stream pat.prange attrs in
      let abs = {t with tm = FPA.Abs ([pat], def) } in
      let rec' = { t with tm = FPA.Name (Pipit_Plugin_Support.rec_lid t.range) } in
      let rec_app = { t with tm = FPA.App (rec', abs, FPA.Nothing) } in
      let letrec = { t with tm = FPA.Let (FPA.NoLetQualifier, [(attrs, (pat, rec_app))], pre_term body) } in
      letrec

  | Let (Rec, binds, body)
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
    { t with tm = If (pre_term p, op, ret, pre_term tru, pre_term fal)}
  | Match (scrut, op, ret, brs) ->
    (* TODO descend into ret *)
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
    let exts = List.mapi (fun i _ -> mk_rec_extract t id0 i) binds in
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


let mk_splice (pat: FPA.pattern) (mode: Pipit_Plugin_Support.mode): FPA.decl' =
  let open FPA in
  let range = pat.prange in
  let level = Expr in
  let rec get_pat p = match p.pat with
   | PatApp (p, _) -> get_pat p
   | PatVar (i, _, _) -> i
   | PatAscribed (p, _) -> get_pat p
   | _ -> FI.mk_ident ("error_pat_not_found", range)
  in
  let id = get_pat pat in
  let fresh = FI.gen' (FI.string_of_id id ^ "_ppt_core") range in
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

let pre_decl (r: FStar_Compiler_Range.range) (d: FPA.decl) =
  match d.d with
  | TopLevelLet (NoLetQualifier, [pat, tm]) ->
    let (pm, _x, pp) = Pipit_Plugin_Support.mode_of_pattern pat in
    if Pipit_Plugin_Support.mode_any_stream pm
    then begin
      let attr = Pipit_Plugin_Support.quote_mode_attr pm r in
      let tm = pre_term tm in
      prerr_endline (FPA.term_to_string tm);
      let splice = { d with d = mk_splice pat pm; attrs = []; quals = [] } in
      Inr [{ d with d = TopLevelLet (NoLetQualifier, [pp, tm]); attrs = attr :: d.attrs };
          splice]
    end
    else
      Inr [d]
    (* pre_let d.drange pat tm *)

  | TopLevelLet (Rec, ps) ->
    (* TODO: check that it is not a stream definition *)
    Inr [d]

  (* TODO: check that streams aren't used in bad positions? *)
  | _ -> Inr [d]


let rec pre_decls_acc (r: FStar_Compiler_Range.range) (ds: FPA.decl list) (acc: FPA.decl list):
  (FPAU.error_message, FPA.decl list) either =
  match ds with
  | [] -> Inr acc
  | d :: ds ->
    match pre_decl r d with
    | Inl err -> Inl err
    | Inr d -> pre_decls_acc r ds (acc @ d)

let pre_decls (r: FStar_Compiler_Range.range) (ds: FPA.decl list):
  (FPAU.error_message, FPA.decl list) either =
  pre_decls_acc r ds []