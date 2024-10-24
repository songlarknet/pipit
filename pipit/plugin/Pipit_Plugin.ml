module PPP  = Pipit_Plugin_Preprocess
module PPT  = Pipit_Plugin_Lift

module FPA  = FStar_Parser_AST
module FPAU = FStar_Parser_AST_Util
module FPPI = FStar_Parser_ParseIt

let parse_decls (contents: string) (r: FStar_Compiler_Range.range)
: (FPAU.error_message, FPA.decl list) FStar_Pervasives.either =
  let res = FPPI.parse_fstar_incrementally.parse_decls contents r in
  match res with
  | Inl err -> Inl err
  | Inr decls -> PPP.pre_decls r decls

let _ = FPAU.register_extension_lang_parser "pipit" { parse_decls = parse_decls }

(* let _ = FStar_Tactics_Native.register_tactic (FStar_Ident.string_of_lid (Pipit_Plugin_Support.lift_tac_lid FStar_Compiler_Range.dummyRange)) (Z.of_int PPT.lift_tac_arity) PPT.lift_tac *)