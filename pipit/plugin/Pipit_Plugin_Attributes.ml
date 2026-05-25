(* Parsing of Pipit-plugin attributes on top-level let bindings.

  The preprocessor runs before name resolution so attribute terms come in
  as raw [FPA.term]s. We match against both the short name (as written by
  users) and the fully-qualified name in [Pipit.Plugin.Interface]. *)

open Fstarcompiler

module FI  = FStarC_Ident
module FPA = FStarC_Parser_AST

type attr_proof_method =
  | Induct1

type attrs = {
  proof : attr_proof_method option;
  proof_expect_failure : bool;
}

let empty : attrs = {
  proof = None;
  proof_expect_failure = false;
}

(* Get the head lident of an attribute term (peeling [Paren]/[App]). *)
let rec head_lid (t: FPA.term) : FI.lident option =
  match t.tm with
  | FPA.Paren t -> head_lid t
  | FPA.App (f, _, _) -> head_lid f
  | FPA.Var l | FPA.Name l -> Some l
  | _ -> None

(* Match an attribute term by short name. Accepts both the unqualified
  form and the FQN [Pipit.Plugin.Interface.<short>]. *)
let attr_matches (short: string) (t: FPA.term) : bool =
  match head_lid t with
  | Some l ->
    let s = FI.string_of_lid l in
    s = short || s = "Pipit.Plugin.Interface." ^ short
  | None -> false

let parse_attributes (terms: FPA.term list) : attrs =
  List.fold_left (fun acc t ->
    if attr_matches "proof_induct1" t
    then { acc with proof = Some Induct1 }
    else if attr_matches "proof_expect_failure" t
    then { acc with proof_expect_failure = true }
    else acc
  ) empty terms

(* Drop all plugin-recognised attribute terms from the list, so they
  aren't forwarded to the underlying [TopLevelLet]. *)
let drop_plugin_attrs (terms: FPA.term list) : FPA.term list =
  List.filter (fun t ->
    not (attr_matches "proof_induct1" t)
    && not (attr_matches "proof_expect_failure" t)
  ) terms
