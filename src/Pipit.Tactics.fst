(* Helper tactics for simplifying Pipit expressions.
   The tactics here are very simple. They just help to massage the transition
   systems in Pipit.System.Exp into a nicer form for the SMT solver. *)
module Pipit.Tactics

module T = FStar.Tactics

module Lift = Pipit.Sugar.Shallow.Tactics.Lift

irreducible
let norm_attr = ()

// Evaluate anything inside Pipit, anything in F*, and anything marked with [@@norm_attr]
let norm_delta_options (namespaces: list string) = [
  delta_namespace ("Pipit" :: "FStar.Pervasives" :: "FStar.List" :: "FStar.Option" :: "FStar.Seq" :: namespaces);
  // Evaluate anything marked [@@norm_attr], explicit core expressions, and typeclass instances
  delta_attr [`%norm_attr; `%Lift.lifted; `%Lift.lifted_prim; `%FStar.Tactics.Typeclasses.tcinstance];
  nbe; zeta; iota; primops
]

(* First stage of normalisation: normalise most things, but avoid unfolding
  any "delayed" applications of PipitRuntime.Prim.p'delay. These delays should
  be placed on most primitives and pattern matches of runtime values. We don't
  want the static structure of Pipit expressions to become nested inside a
  pattern match on a runtime value, because then the normaliser isn't able to
  evaluate as eagerly - it doesn't know if the branch is impossible. *)
let norm_phase_pre (namespaces: list string) =
  T.norm (norm_delta_options namespaces)
  // XXX: want to apply some rewrites too:
  // T.l_to_r [`Pipit.Sugar.Shallow.lemma_unsafe_proposition_holds]

(* Final stage of normalisation: unwrap the delayed applications and perform
  minimal normalisation. *)
let norm_phase_post () =
  // XXX: does this need zeta_full to force descending into matches?
  T.norm [delta_only [`%PipitRuntime.Prim.p'delay]]

let norm_full (namespaces: list string) =
  norm_phase_pre namespaces;
  norm_phase_post ()


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
      | _ ->
        (* Check if a named user-defined type has one or fewer constructor.
          If so, we can safely destruct it without introducing any new goals. *)
        (match T.lookup_typ (T.cur_env ()) nm with
        | None ->
          false
        | Some se -> (match T.inspect_sigelt se with
          | T.Sg_Inductive _name _univs _binders _typ []
          | T.Sg_Inductive _name _univs _binders _typ [_]
            -> true
          | _ -> false))
    end
  | T.Tv_App f _ -> type_is_product f
  | T.Tv_Const T.C_Unit -> true
  | T.Tv_Refine _ t _ -> type_is_product t
  | _ ->
    false

(* Break apart any product types bound in `b`. *)
let rec tac_break_binder (b: T.binder): T.Tac unit =
  let open T in
  let open FStar.List.Tot in
  let tm = T.binder_to_term b in
  let ty = T.type_of_binder b in
  if type_is_product ty
  then begin
    T.destruct tm;
    tac_break_intros ();
    ignore (T.trytac (fun () -> clear b))
  end

and tac_break_intros (): T.Tac unit =
  match T.trytac T.intro with
  | None -> ()
  | Some b -> begin
    match T.term_as_formula (T.type_of_binder b) with
    | T.Comp (T.Eq _) _ _ ->
      T.rewrite b;
      ignore (T.trytac (fun () -> T.clear b));
      ()
    | _ ->
      tac_break_binder b;
      tac_break_intros ()
  end

let tac_break_top (): T.Tac unit =
  T.repeat' T.revert;
  tac_break_intros ()


(* For some reason, these guys need to be explicitly unfolded here *)
let tac_tricky_unfolds (): T.Tac unit =
    T.norm [
           delta_fully ["Pipit.System.Ind.step_case_k'";
                        "Pipit.System.Ind.base_case_k'";
                        ];
           zeta]

let rec tac_descend (break_binder: T.binder -> T.Tac unit) (norm: unit -> T.Tac unit): T.Tac unit =
  let go () = tac_descend break_binder norm in
  norm ();
  let g = T.cur_goal () in
  let f = T.term_as_formula g in
  match f with
  | T.And _ _ ->
    T.seq T.split go
  | T.Forall _ _ _ ->
    let b = T.forall_intro () in
    break_binder b;
    go ()
  // Pulling the implication lhs into the environment is a bit annoying because
  // then subsequent calls to `norm` won't normalise it.
  // Disable for now
  // | T.Implies _ _ ->
  //   let b = T.implies_intro () in
  //   break_binder b;
  //   go ()
  | _ ->
    ()

(* Prove a transition system. We want to ensure that the translation
   to transition system and all of the definitions are normalised
   away. This turns out to be surprisingly simple, and we just
   need to explicitly unfold a few definitions that are otherwise ignored
   by the normalisation heuristics.
   Breaking apart the products is sometimes helpful for debugging,
   but doesn't seem to be necessary for actual proofs.
   *)
let pipit_simplify (namespaces: list string): T.Tac unit =
  T.seq (fun _ -> tac_descend (fun _ -> ()) (fun _ -> norm_phase_pre namespaces))
    norm_phase_post


let pipit_simplify_products (namespaces: list string): T.Tac unit =
  tac_break_top ();
  T.seq (fun _ -> tac_descend (fun b -> tac_break_binder b) (fun _ -> norm_phase_pre namespaces))
    norm_phase_post

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
  go (List.Tot.rev bs)

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
