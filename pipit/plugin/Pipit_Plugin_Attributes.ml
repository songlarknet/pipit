(* Parsing of Pipit-plugin attributes on top-level let bindings.

  The preprocessor runs before name resolution so attribute terms come in
  as raw [FPA.term]s. We match against both the short name (as written by
  users) and the fully-qualified name in [Pipit.Plugin.Interface]. *)

open Fstarcompiler

module FI  = FStarC_Ident
module FPA = FStarC_Parser_AST

type attr_proof_method =
  | Induct1
  | Contract of { rely: FI.ident; guar: FI.ident }

type attrs = {
  proof : attr_proof_method option;
  proof_expect_failure : bool;
  derive_has_stream : bool;
}

let empty : attrs = {
  proof = None;
  proof_expect_failure = false;
  derive_has_stream = false;
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

(* Pull the (possibly qualified) ident out of a `\`%nm` term, which the
  parser emits as `VQuote (Var nm)`. Returns the *last* component, since
  that's what users actually write at the splice site. *)
let rec ident_of_vquote (t: FPA.term): FI.ident option =
  match t.tm with
  | FPA.Paren t -> ident_of_vquote t
  | FPA.VQuote q ->
    (match q.tm with
     | FPA.Var lid | FPA.Name lid -> Some (FI.ident_of_lid lid)
     | _ -> None)
  | _ -> None

(* Collect the (head, args) of a left-nested application, peeling Paren. *)
let collect_app (t: FPA.term): FPA.term * FPA.term list =
  let rec go (t: FPA.term) acc =
    match t.tm with
    | FPA.Paren t -> go t acc
    | FPA.App (f, a, _) -> go f (a :: acc)
    | _ -> (t, acc)
  in
  go t []

(* Parse a `proof_contract (`%rely) (`%guar)` attribute. *)
let parse_proof_contract (t: FPA.term): (FI.ident * FI.ident) option =
  let (head, args) = collect_app t in
  if not (attr_matches "proof_contract" head) then None
  else match args with
    | [a1; a2] ->
      (match ident_of_vquote a1, ident_of_vquote a2 with
       | Some r, Some g -> Some (r, g)
       | _ ->
         failwith "Pipit plugin: proof_contract requires two `%name vquoted args")
    | _ ->
      failwith "Pipit plugin: proof_contract takes exactly two `%name args (rely, guar)"

let parse_attributes (terms: FPA.term list) : attrs =
  List.fold_left (fun acc t ->
    if attr_matches "proof_induct1" t
    then { acc with proof = Some Induct1 }
    else if attr_matches "proof_contract" t
    then
      (match parse_proof_contract t with
       | Some (rely, guar) -> { acc with proof = Some (Contract { rely; guar }) }
       | None -> acc)
    else if attr_matches "proof_expect_failure" t
    then { acc with proof_expect_failure = true }
    else if attr_matches "derive_has_stream" t
    then { acc with derive_has_stream = true }
    else acc
  ) empty terms

(* Drop all plugin-recognised attribute terms from the list, so they
  aren't forwarded to the underlying [TopLevelLet]. *)
let drop_plugin_attrs (terms: FPA.term list) : FPA.term list =
  List.filter (fun t ->
    not (attr_matches "proof_induct1" t)
    && not (attr_matches "proof_contract" t)
    && not (attr_matches "proof_expect_failure" t)
    && not (attr_matches "derive_has_stream" t)
  ) terms
