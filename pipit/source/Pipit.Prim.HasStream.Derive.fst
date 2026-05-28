(* Splice tactics for auto-generating [has_stream] instances for user-defined
  types.

  Supported (currently monomorphic only):
    * single-constructor inductives (records, data classes / structs) via
      [derive_has_stream "T"].
    * multi-constructor inductives where the user picks a default ctor by
      name via [derive_has_stream_with_default "T" "Ctor"].

  Each constructor argument must itself have a [has_stream] instance in
  scope; the synthesised instance fills each ctor argument with
  [PSSB.val_default] and lets F* resolve the typeclass per position.

  Usage from a [#lang-pipit] module:

    type my_record = { x: int; y: int; }
    %splice[has_stream_my_record] (derive_has_stream "my_record")

    type my_sum = | A | B: int -> my_sum
    %splice[has_stream_my_sum] (derive_has_stream_with_default "my_sum" "A")

  Polymorphic inductives are not yet supported; see project notes. *)
module Pipit.Prim.HasStream.Derive

module Tac  = FStar.Tactics.V2
module Ref  = FStar.Reflection.V2
module List = FStar.List.Tot

module PSSB = Pipit.Prim.HasStream
module PTB  = Pipit.Tactics.Base

open FStar.Tactics.NamedView


(* Build the term [Ctor PSSB.val_default ... PSSB.val_default] with one
  argument per binder in [bs]. Each occurrence of [PSSB.val_default] is left
  with its [#a] and [{| has_stream a |}] implicits unresolved so that F*'s
  typeclass resolution picks the right instance for each argument position
  when the spliced sigelt is typechecked. *)
let rec mk_default_app (head: Tac.term) (bs: list Tac.binder): Tac.Tac Tac.term =
  match bs with
  | [] -> head
  | _ :: bs' ->
    let arg = `(PSSB.val_default) in
    let app = Tac.pack (Tac.Tv_App head (arg, Ref.Q_Explicit)) in
    mk_default_app app bs'


(* Look up an inductive definition in the current module. Fails with a
  useful error if [nm] is not an [Sg_Inductive] or is polymorphic. *)
let lookup_monomorphic_inductive (nm: string): Tac.Tac (Tac.name & list (Tac.name & Tac.typ)) =
  let m       = Tac.cur_module () in
  let ty_name = List.append m [nm] in
  let env     = Tac.top_env () in
  let se = match Ref.lookup_typ env ty_name with
    | None ->
      Tac.fail ("derive_has_stream: type not found in current module: " ^ nm)
    | Some se -> se
  in
  match Tac.inspect_sigelt se with
  | Sg_Inductive { nm = nm_ind; params; ctors } ->
    if Cons? params then
      Tac.fail ("derive_has_stream: " ^ nm ^
                ": polymorphic types are not yet supported")
    else
      nm_ind, ctors
  | _ ->
    Tac.fail ("derive_has_stream: " ^ nm ^ ": expected an inductive type")


(* Build the [Sg_Let] sigelt for [instance has_stream_<short_nm>], given
  the resolved type name, the chosen ctor, and the ctor's type. *)
let mk_instance_sigelt
  (short_nm: string)
  (nm_inductive: Tac.name)
  (ctor_nm: Tac.name)
  (ctor_ty: Tac.typ)
  : Tac.Tac Tac.sigelt
  =
  let m = Tac.cur_module () in
  let bs, _ = Tac.collect_arr_bs ctor_ty in
  let ctor_hd  = Tac.pack (Tac.Tv_FVar (Tac.pack_fv ctor_nm)) in
  let default_app = mk_default_app ctor_hd bs in
  let ty_hd  = Tac.pack (Tac.Tv_FVar (Tac.pack_fv nm_inductive)) in
  let nm_str = Tac.pack (Tac.Tv_Const (Ref.C_String (Ref.implode_qn nm_inductive))) in
  let body = `({
    ty_id       = [(`#nm_str)];
    val_default = (`#default_app);
  } <: PSSB.has_stream (`#ty_hd)) in
  let inst_nm = List.append m [ "has_stream_" ^ short_nm ] in
  let lb: Tac.letbinding = {
    lb_fv  = Tac.pack_fv inst_nm;
    lb_us  = [];
    lb_typ = Tac.pack Tac.Tv_Unknown;
    lb_def = body;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let { isrec = false; lbs = [lb] } in
  let se = Tac.pack_sigelt sv in
  Ref.set_sigelt_attrs [`FStar.Tactics.Typeclasses.tcinstance] se


(* True iff the qualified name [nm] ends in the short name [short]. *)
let ctor_short_matches (short: string) (nm: Tac.name): bool =
  match List.rev nm with
  | hd :: _ -> hd = short
  | [] -> false


(* Generate a [has_stream T] instance for a single-constructor inductive
  [T] defined in the current module. *)
let derive_has_stream (nm: string): Tac.Tac (list Tac.sigelt) =
  let nm_inductive, ctors = lookup_monomorphic_inductive nm in
  let ctor_nm, ctor_ty = match ctors with
    | [c] -> c
    | _ ->
      Tac.fail ("derive_has_stream: " ^ nm ^
                ": expected exactly one constructor, got " ^
                string_of_int (List.length ctors) ^
                "; use derive_has_stream_with_default to pick one")
  in
  [mk_instance_sigelt nm nm_inductive ctor_nm ctor_ty]


(* Generate a [has_stream T] instance for a multi-constructor inductive
  [T] defined in the current module. The default value is built from the
  constructor named [default_ctor] (short name) with [PSSB.val_default]
  in each argument position; the nicest choice is usually a nullary ctor. *)
let derive_has_stream_with_default
  (nm: string)
  (default_ctor: string)
  : Tac.Tac (list Tac.sigelt)
  =
  let nm_inductive, ctors = lookup_monomorphic_inductive nm in
  let chosen =
    List.find (fun (cn, _) -> ctor_short_matches default_ctor cn) ctors
  in
  let ctor_nm, ctor_ty = match chosen with
    | Some c -> c
    | None ->
      Tac.fail ("derive_has_stream_with_default: " ^ nm ^
                ": no constructor named " ^ default_ctor)
  in
  [mk_instance_sigelt nm nm_inductive ctor_nm ctor_ty]
