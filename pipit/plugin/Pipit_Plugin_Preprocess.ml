open FStar_Pervasives

module FCE  = FStar_Compiler_Effect
module FPA  = FStar_Parser_AST
module FPAU = FStar_Parser_AST_Util
module FI   = FStar_Ident
module FC   = FStar_Const

let pre_term (tm: FPA.term) =
  tm

(* let pre_splice (r: FStar_Compiler_Range.range) (id: FI.ident) *)
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
    [mk_id_str id; mk_id_str fresh; Pipit_Plugin_Support.quote_mode mode range]
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
    let (pm, pp) = Pipit_Plugin_Support.mode_of_pattern pat in
    if Pipit_Plugin_Support.mode_any_stream pm
    then begin
      let attr = Pipit_Plugin_Support.quote_mode_attr pm r in
      let tm = pre_term tm in
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