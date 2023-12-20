(* Helper tactics for simplifying Pipit expressions.
   The tactics here are very simple. They just help to massage the transition
   systems in Pipit.System.Exp into a nicer form for the SMT solver. *)
module Pipit.Tactics

module T = FStar.Tactics

irreducible
let norm_attr = ()

// Evaluate anything inside Pipit, anything in F*, and anything marked with [@@norm_attr]
let norm_delta_options (namespaces: list string) = [delta_namespace ("Pipit" :: "FStar.Pervasives" :: "FStar.List" :: "FStar.Option" :: "FStar.Seq" :: namespaces); delta_attr [`%norm_attr]; nbe; zeta; iota; primops]

(* Re-exports *)
let norm_full (namespaces: list string) =
  T.norm (norm_delta_options namespaces)


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
   // if type_is_unit ty
   // then begin
   //   (try clear b with | _ -> ());
   //   tac_products bs
   // end
   // else
   if type_is_product ty
   then begin
    T.destruct tm;
    let bs' = T.repeat T.intro in
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

(* For some reason, these guys need to be explicitly unfolded here *)
let tac_tricky_unfolds (): T.Tac unit =
    T.norm [
           delta_fully ["Pipit.System.Ind.step_case_k'";
                        "Pipit.System.Ind.base_case_k'";
                        ];
           zeta]

(* Prove a transition system. We want to ensure that the translation
   to transition system and all of the definitions are normalised
   away. This turns out to be surprisingly simple, and we just
   need to explicitly unfold a few definitions that are otherwise ignored
   by the normalisation heuristics.
   Breaking apart the products is sometimes helpful for debugging,
   but doesn't seem to be necessary for actual proofs.
   *)
let pipit_simplify (namespaces: list string): T.Tac unit =
  T.repeatseq (fun _ ->
    norm_full namespaces;
    tac_tricky_unfolds ();
    let b = T.forall_intro () in
    // tac_products [b];
    ())


let pipit_simplify_products (namespaces: list string): T.Tac unit =
  T.repeatseq (fun _ ->
    norm_full namespaces;
    tac_tricky_unfolds ();
    let b = T.forall_intro () in
    tac_products [b];
    ())

// NB: this causes --extract krml to crash, so need both noextract attributes
noextract
[@@noextract_to "krml"]
let clear_all (): T.Tac unit =
  let open T in
  let rec go bs: Tac unit = match bs with
   | [] -> ()
   | b::bs ->
    (try
      T.clear b
    with err ->
      // T.print (T.term_to_string (quote err));
      ());
    go bs
  in
  ignore (T.repeat T.revert);
  let bs = T.repeat T.intro in
  go bs

(* Left-to-right, top-down; see FStar.Tactics.l_to_r, which is the bottom-up version. *)
let top_down (lems: list T.term): T.Tac unit =
  let first_or_trefl () : T.Tac unit =
      T.fold_left (fun k l () ->
                  (fun () -> T.apply_lemma_rw l)
                  `T.or_else` k)
                T.trefl lems () in
  T.t_pointwise T.TopDown first_or_trefl

(* Rewrite left-to-right, top-down in environment. This tactic first reverts
  all binders into the goal, performs the rewrite, and then re-introduces the
  binders. See also FStar.Tactics.l_to_r *)
let top_down_in_env (lems:list T.term): T.Tac unit =
  ignore (T.repeat T.revert);
  top_down lems;
  ignore (T.repeat T.intro)
