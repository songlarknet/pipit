(* Handwritten registration for the `#lang-pipit` extension.

   This is the "tiny bit of handwritten OCaml" that packages the extracted core
   (`Pipit_Exp_Base`, generated into `generated/`) into a loadable F* language
   plugin. For now the parser is a passthrough: a `#lang-pipit` module is parsed
   exactly as ordinary F*. This is enough to register the language name; source
   preprocessing / lifting is added later.

   Mirrors pipit 1's `pipit/plugin/Pipit_Plugin.ml`, minus the preprocessing
   step. *)

open Fstarcompiler

module FPA  = FStarC_Parser_AST
module FPAU = FStarC_Parser_AST_Util
module FPPI = FStarC_Parser_ParseIt

let parse_decls (contents: string) (r: FStarC_Range.range)
: (FPAU.error_message, FPA.decl list) FStar_Pervasives.either =
  FPPI.parse_fstar_incrementally.parse_decls contents r

let _ = FPAU.register_extension_lang_parser "pipit" { parse_decls = parse_decls }
