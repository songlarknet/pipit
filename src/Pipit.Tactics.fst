(* Helper tactics for simplifying Pipit expressions.
   The tactics here are very simple. They just help to massage the transition
   systems in Pipit.System.Exp into a nicer form for the SMT solver. *)
module Pipit.Tactics

module T = FStar.Tactics

(* Re-exports *)
let norm_full () = T.norm [delta; nbe; zeta; iota; primops]

let dump s = T.dump s

let dump_ () = dump "-"

(* Check if a type is a tuple or unit type that we want the tactics to break
   apart. *)
let rec type_is_product (ty: T.typ): T.Tac bool =
  match T.inspect_unascribe ty with
  | T.Tv_FVar fv | T.Tv_UInst fv _ ->
    let nm = T.inspect_fv fv in
    begin
      match nm with
      | ["FStar"; "Pervasives"; "Native"; tt ] ->
        tt <> "option"
      // | ["Prims"; "unit"] ->
      //  true
      // See Pipit.System.Base.fst.
      | ["Pipit"; "System"; "Base"; "system_then_state" ] ->
        true
      | _ -> false
    end
  | T.Tv_App f _ -> type_is_product f
  | T.Tv_Const T.C_Unit -> true
  | _ ->
    false

(* Check if type is unit *)
let type_is_unit (ty: T.typ): T.Tac bool =
  match T.inspect_unascribe ty with
  | T.Tv_FVar fv | T.Tv_UInst fv _ ->
    let nm = T.inspect_fv fv in
    begin
      match nm with
      | ["Prims"; "unit"] ->
        true
      | _ -> false
    end
  | _ ->
    false

(* Break apart any product types bound in `bs`. *)
let rec tac_products (bs: list T.binder): T.Tac unit = match bs with
 | [] -> ()
 | b :: bs ->
   let open T in
   let open FStar.List.Tot in
   let tm = T.binder_to_term b in
   let ty = T.type_of_binder b in
   if type_is_unit ty
   then begin
     (try clear b with | _ -> ());
     tac_products bs
   end
   else if type_is_product ty
   then begin
    T.destruct tm;
    let bs' = T.repeat T.intro in
    T.rewrite_all_context_equalities bs';
    T.norm [iota];
    let _ = T.trytac (fun () ->
      match List.Tot.rev bs' with
      | breq :: _ -> rewrite breq; clear breq; clear b
      | _ -> clear b
    ) in
    tac_products (bs' @ bs)
   end
   else begin
    tac_products bs
   end

let tac_intros_smash (): T.Tac unit =
  T.repeatseq (fun _ ->
    let b = T.forall_intro () in
    tac_products [b])

(* Introduce foralls and try to simplify them *)
let rec pipit_simplify' (n: nat): T.Tac unit =
  match n with
  | 0 -> ()
  | _ ->
    let open T in
    norm_full ();
    try
        let b = forall_intro () in
        tac_products [b];
        pipit_simplify' (n - 1)
    with _ -> ()

let pipit_simplify (): T.Tac unit = pipit_simplify' 5
