module PPP  = Pipit_Plugin_Preprocess

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
