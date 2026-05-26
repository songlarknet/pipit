(* Splice tactics for auto-generating [has_stream] instances for user-defined
  types.

  Phase 1 supports monomorphic single-constructor inductives (records and
  data classes / structs). Each constructor argument must itself have a
  [has_stream] instance in scope; the synthesised instance fills each
  position with [PSSB.val_default] and lets F* resolve the typeclass.

  Usage from a [#lang-pipit] module:

    type my_record = { x: int; y: int; }
    %splice[has_stream_my_record] (derive_has_stream "my_record")

  Polymorphic types and multi-constructor sums are out of scope here; see
  the project notes for follow-up phases. *)
module Pipit.Sugar.Shallow.Tactics.Derive

module Tac  = FStar.Tactics.V2
module Ref  = FStar.Reflection.V2
module List = FStar.List.Tot

module PSSB = Pipit.Sugar.Shallow.Base
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


(* Generate a [has_stream T] instance for a single-constructor inductive
  [T] defined in the current module. *)
let derive_has_stream (nm: string): Tac.Tac (list Tac.sigelt) =
  let m       = Tac.cur_module () in
  let ty_name = List.append m [nm] in
  let env     = Tac.top_env () in
  let se = match Ref.lookup_typ env ty_name with
    | None ->
      Tac.fail ("derive_has_stream: type not found in current module: " ^ nm)
    | Some se -> se
  in
  let nm_inductive, ctor_nm, ctor_ty =
    match Tac.inspect_sigelt se with
    | Sg_Inductive { nm = nm_ind; params; ctors } ->
      if Cons? params then
        Tac.fail ("derive_has_stream: " ^ nm ^
                  ": polymorphic types are not yet supported (Phase 3)")
      else
        (match ctors with
         | [(cn, ct)] -> nm_ind, cn, ct
         | _ ->
           Tac.fail ("derive_has_stream: " ^ nm ^
                     ": only single-constructor inductives are supported, got " ^
                     string_of_int (List.length ctors) ^ " constructors"))
    | _ ->
      Tac.fail ("derive_has_stream: " ^ nm ^ ": expected an inductive type")
  in
  let bs, _ = Tac.collect_arr_bs ctor_ty in
  let ctor_hd  = Tac.pack (Tac.Tv_FVar (Tac.pack_fv ctor_nm)) in
  let default_app = mk_default_app ctor_hd bs in
  let ty_hd  = Tac.pack (Tac.Tv_FVar (Tac.pack_fv nm_inductive)) in
  let nm_str = Tac.pack (Tac.Tv_Const (Ref.C_String (Ref.implode_qn nm_inductive))) in
  let body = `({
    ty_id       = [(`#nm_str)];
    val_default = (`#default_app);
  } <: PSSB.has_stream (`#ty_hd)) in
  let inst_nm = List.append m [ "has_stream_" ^ nm ] in
  let lb: Tac.letbinding = {
    lb_fv  = Tac.pack_fv inst_nm;
    lb_us  = [];
    lb_typ = Tac.pack Tac.Tv_Unknown;
    lb_def = body;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let { isrec = false; lbs = [lb] } in
  let se = Tac.pack_sigelt sv in
  let se = Ref.set_sigelt_attrs [`FStar.Tactics.Typeclasses.tcinstance] se in
  [se]
