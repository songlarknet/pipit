module Pipit.Tactics.Cse

module PTB = Pipit.Tactics.Base

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2
module TermEq = FStar.Reflection.V2.TermEq

module Range = FStar.Range

module List = FStar.List.Tot


let fail (#a: Type) (msg: string) (rng: Range.range) (ctx: list string): Tac.Tac a =
  let str0 = "CSE transform: failure at " ^ Tac.range_to_string rng ^ "\n  " ^ msg in
  let str = List.fold_left (fun str str' -> str ^ "\n    * " ^ str') str0 ctx in
  Tac.fail str

let debug_print (str: unit -> Tac.Tac string): Tac.Tac unit =
  if Tac.ext_getv "pipit:cse:debug" <> ""
  then (
    let ms = Tac.curms () in
    Tac.print (Tac.term_to_string (quote ms) ^ ": " ^ str ())
  )

// todo better repr?
let fv_set = list nat

noeq
type subexp_bind = {
  uniq: nat;
  namedv: Tac.namedv;
  term_of_uniq: Tac.term;
  term_of_def: Tac.term;
  fvs_of_def: fv_set;
}

type binds = list subexp_bind

let rec fvs_of_pat (p: Tac.pattern): Tac.Tac fv_set =
  match p with
  | Tac.Pat_Constant _ -> []
  | Tac.Pat_Cons c ->
    Tac.fold_left (fun c (p,_) -> List.(fvs_of_pat p @ c)) [] c.subpats
  | Tac.Pat_Var v -> [v.v.uniq]
  | Tac.Pat_Dot_Term _ -> []

let close1 (b: subexp_bind) (tm: Tac.term): Tac.term =
  Tac.Tv_Let false [] (Tac.namedv_to_binder b.namedv (`_)) b.term_of_def tm

let rec close_all (tm: Tac.term) (bs: binds) (fvs: fv_set): Tac.Tac (Tac.term & fv_set) =
  match bs with
  | [] ->
    (tm, fvs)
  | b :: bs ->
    let (tm, fvs) = close_all tm bs List.(b.fvs_of_def @ fvs) in
    (close1 b tm, fvs)

let rec close_dependents (tm: Tac.term) (bs acc: binds) (fvs fv_closing: fv_set): Tac.Tac (Tac.term & binds & fv_set) =
  match bs with
  | [] ->
    (tm, List.rev acc, fvs)
  | b :: bs ->
    let u = b.uniq in
    if List.existsb (fun c -> List.mem c b.fvs_of_def) fv_closing
    then
      let (tm, bs', fv) = close_dependents tm bs acc List.(b.fvs_of_def @ fvs) (b.uniq :: fv_closing) in
      (close1 b tm, bs', fv)
    else
      close_dependents tm bs (b :: acc) fvs fv_closing

let term_matches (t u: Tac.term): Tac.Tac bool =
  // do not consider Unknowns
  match Tac.inspect t with
  | Tac.Tv_Unknown -> false
  | _ -> TermEq.term_eq t u


let rec find (t: Tac.term) (bs: binds) (fvs: fv_set): Tac.Tac (option (Tac.term & binds & fv_set)) =
  match bs with
  | [] -> None
  | b :: bs ->
    if term_matches b.term_of_def t
    then Some (b.term_of_uniq, [], [b.uniq])
    else find t bs fvs

let find_or_bind (t: Tac.term) (bs_pre bs_post: binds) (fvs: fv_set): Tac.Tac (Tac.term & binds & fv_set) =
  match find t bs_pre fvs with
  | Some r ->
    Tac.print ("find_or_bind: found" ^ Tac.term_to_string (quote r));
    r
  | None ->
    Tac.print ("find_or_bind: none for " ^ Tac.term_to_string (quote t));
    let uniq = Tac.fresh () in
    let namedv: Tac.namedv =
      { uniq = uniq; sort = Tac.seal (`_); ppname = Ref.as_ppname ("cse" ^ string_of_int uniq); } in
    let term_of_uniq = Tac.pack (Tac.Tv_Var namedv) in
    let term_of_def  = t in
    let b = { uniq; namedv; term_of_uniq; term_of_def; fvs_of_def = fvs; } in
    let bs' = List.(bs_post @ [b]) in
    (term_of_uniq, bs', [uniq])


let rec cse_tm (t: Tac.term) (bs: binds): Tac.Tac (Tac.term & binds & fv_set) =
  let ti = Tac.inspect t in
  match Tac.inspect t with
  | Tac.Tv_Var (v: Tac.namedv) ->
    (t, [], [v.uniq])
  | Tac.Tv_BVar (v: Tac.bv) ->
    fail
      ("unexpected bvar; expected named variables only " ^ Tac.term_to_string t)
      (Ref.range_of_term t) []
  | Tac.Tv_FVar _ | Tac.Tv_UInst _ _ | Tac.Tv_Const _ ->
    (t, [], [])

  | Tac.Tv_App _ _ ->
    let (hd, args) = Tac.collect_app ti in
    let (hd,  hb, hfv) = cse_tm hd  bs in
    let (tm, bs', fvs) = Tac.fold_left (fun (tm, bs', fvs) (arg, aqual) ->
      let (arg, ab, afv) = cse_tm arg List.(bs @ bs') in
      (Tac.pack (Tac.Tv_App tm (arg, aqual)), List.(bs' @ ab), List.(fvs @ afv)))
      (hd, hb, hfv) args
    in
    Tac.print ("is_type: " ^ Tac.term_to_string hd);
    let is_type_ctor =
      match Tac.inspect hd with
      | Tac.Tv_FVar _ ->
        let ty = Tac.tc (Tac.top_env ()) hd in
        let (targ, tres) = Tac.collect_arr ty in
        (match tres with
        | Tac.C_Total t ->
        Tac.print ("is_type: returns: " ^ Tac.term_to_string t);
        (match Tac.inspect t with
        | Tac.Tv_Type _ ->
          true
        | _ -> TermEq.term_eq t (`Prims.eqtype))
        | _ -> false)
      | _ -> false
    in
    if is_type_ctor
    then (tm, bs', fvs)
    else find_or_bind tm bs bs' fvs


  | Tac.Tv_Abs bv tm ->
    let (tm, bs', fvs) = cse_tm tm bs in
    let u = bv.uniq in
    Tac.print ("abs: closing binder " ^ Tac.term_to_string (quote u));
    Tac.print ("abs: bindings " ^ Tac.term_to_string (quote bs'));
    let (tm, bs', fvs) = close_dependents tm bs' [] fvs [bv.uniq] in
    (Tac.pack (Tac.Tv_Abs bv tm), bs', fvs)

  | Tac.Tv_Let true attrs b def body ->
  // DUP: we can't define mutually recursive letrecs, so we have to close b inside each subterm
    let (dtm, dbs, dfv) = cse_tm def bs in
    let (dtm, dbs, dfv) = close_dependents dtm dbs [] dfv [b.uniq] in
    let (btm, bbs, bfv) = cse_tm body List.(bs @ dbs) in
    let (btm, bbs, bfv) = close_dependents btm bbs [] bfv [b.uniq] in
    (Tac.pack (Tac.Tv_Let true attrs b dtm btm), List.(dbs @ bbs), List.(dfv @ bfv))

  | Tac.Tv_Let false attrs b def body ->
    let u = b.uniq in
    Tac.print ("let: binder " ^ Tac.term_to_string (quote u));
    Tac.print ("let: def " ^ Tac.term_to_string (quote def));
    let (dtm, dbs, dfv) = cse_tm def bs in
    let (btm, bbs, bfv) = cse_tm body List.(bs @ dbs) in
    let (btm, bbs, bfv) = close_dependents btm bbs [] bfv [b.uniq] in
    (Tac.pack (Tac.Tv_Let false attrs b dtm btm), List.(dbs @ bbs), List.(dfv @ bfv))

  | Tac.Tv_Match scrut ret brs ->
    let (scrut, sbs, sfv) = cse_tm scrut bs in
    let bs' = List.(bs @ sbs) in
    let (brs, fvs) = Tac.fold_left (fun (brs, fvs) (pat, ptm) ->
      let (ptm, pbs, pfv) = cse_tm ptm bs' in
      Tac.print ("in match: bs' " ^ Tac.term_to_string (quote bs'));
      Tac.print ("in match: pbs " ^ Tac.term_to_string (quote pbs));
      // For match branches, it's safer to include all of the branch's bindings here.
      // Some applications, such as recursive calls, really can't be moved outside of
      // their branch, or we lose the information about them being terminating.
      let (ptm,      pfv) = close_all ptm pbs pfv in
      // let (ptm, pbs, pfv) = close_dependents ptm pbs [] pfv (fvs_of_pat pat) in
      ((pat, ptm) :: brs, List.(fvs @ pfv)))
      ([], sfv)
      (List.rev brs)
    in
    let tm = Tac.pack (Tac.Tv_Match scrut ret brs) in
    find_or_bind tm bs sbs fvs

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    let (tm, tmbs, tmfv) = cse_tm tm bs in
    let (ty, tybs, tyfv) = cse_tm ty bs in
    // TODO descend into tac
    (Tac.pack (Tac.Tv_AscribedT tm ty tac use_eq), List.(tmbs @ tybs), List.(tmfv @ tyfv))

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    // TODO descend into tac, cmp
    let (tm, tmbs, tmfv) = cse_tm tm bs in
    (Tac.pack (Tac.Tv_AscribedC tm cmp tac use_eq), tmbs, tmfv)

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _
  | Tac.Tv_Arrow  _ _
  | Tac.Tv_Type   _
  | Tac.Tv_Refine _ _
  | Tac.Tv_Unknown     ->
    // TODO: descend into arrows, refinements
    (t, [], [])

  | Tac.Tv_Unsupp ->
    fail ("CSE failed: cannot inspect term: " ^ Tac.term_to_string t)
      (Ref.range_of_term t) ["(unsupported term)"]


let cse (tm: Tac.term): Tac.Tac Tac.term =
  let (tm, bs, _) = cse_tm tm [] in
  let (tm, _) = close_all tm bs [] in
  Tac.print ("CSE: " ^ Tac.term_to_string tm);
  // debug_print (fun _ -> "CSE: " ^ Tac.term_to_string tm);
  tm


let cse_bind1 (nm nm_cse: string): Tac.Tac Tac.sigelt =
  let lb_src = PTB.lookup_lb_top (Tac.top_env ()) (Ref.explode_qn nm) in

  let cse_def = cse lb_src.lb_def in
  debug_print (fun () -> "cse is: " ^ Tac.term_to_string cse_def);

  let ty = Tac.pack Tac.Tv_Unknown in

  // TODO: support recursive bindings
  let lb_core: Tac.letbinding = {
    lb_fv  = Tac.pack_fv (Ref.explode_qn nm_cse);
    lb_us  = lb_src.lb_us;
    lb_typ = ty;
    lb_def = cse_def;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let {isrec=false; lbs=[lb_core]} in
  let se: Tac.sigelt = Tac.pack_sigelt sv in
  let nm_src_const = Tac.pack (Tac.Tv_Const (Ref.C_String nm)) in
  let attrs = [] in
  debug_print (fun () -> "DONE: " ^ nm_cse);
  Ref.set_sigelt_attrs attrs se

let cse_binds (nms: list string): Tac.Tac (list Tac.sigelt) =
  Tac.map (fun nm -> cse_bind1 nm (nm ^ "_cse")) nms
