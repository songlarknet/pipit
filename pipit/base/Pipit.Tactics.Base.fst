module Pipit.Tactics.Base

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2

module List = FStar.List.Tot


let rec mk_abs_list (bs: list Tac.binder) (tm: Tac.term): Tac.term =
  match bs with
  | bv :: bs ->
    Tac.pack (Tac.Tv_Abs bv (mk_abs_list bs tm))
  | [] -> tm

let rec mk_apps_of_binders (bs: list Tac.binder) (tm: Tac.term): Tac.term =
  match bs with
  | bv :: bs ->
    let arg = Tac.pack (Tac.Tv_Var bv) in
    let qual = match bv.qual with
      | Ref.Q_Meta _ -> Ref.Q_Implicit
      | q -> q
    in
    let tm  = Tac.pack (Tac.Tv_App tm (arg, qual)) in
    mk_apps_of_binders bs tm
  | [] -> tm

let eta_expand_binders (bs: list Tac.binder) (tm: Tac.term): Tac.term =
  mk_abs_list bs (mk_apps_of_binders bs tm)

let eta_expand (tm ty: Tac.term): Tac.Tac Tac.term =
  let (bs,cmp)= Tac.collect_arr_bs ty in
  eta_expand_binders bs tm

let qual_is_explicit (q: Ref.aqualv): bool =
  match q with
  | Ref.Q_Explicit -> true
  | _ -> false

let unwrap_AscribeT (tm: Tac.term): Tac.Tac Tac.term =
  match Tac.inspect tm with
  | Tac.Tv_AscribedT tm _ _ _ -> tm
  | _ -> tm

(* Try to get the type of a term. If the term is a type ascription (tm <: ty) then
  return the type ty as-is without bothering to check tm. *)
let tc_unascribe (e: Tac.env) (tm: Tac.term): Tac.Tac Tac.term =
  match Tac.inspect tm with
  | Tac.Tv_AscribedT _ ty _ _
  | Tac.Tv_AscribedC _ (Tac.C_Total ty) _ _ ->
    ty
  | _ ->
    let ty = Tac.tc e tm in
    ty

let returns_of_comp (c: Tac.comp): Tac.term =
  match c with
  | Tac.C_Total t
  | Tac.C_GTotal t
  | Tac.C_Eff _ _ t _ _ -> t
  | Tac.C_Lemma _ _ _ -> (`unit)

let lookup_lb_top (e: Tac.env) (nm: Ref.name): Tac.Tac Tac.letbinding =
  match Ref.lookup_typ e nm with
  | None -> Tac.fail ("lookup_lb_top: no such top-level binding " ^ Ref.implode_qn nm)
  | Some se ->
    match Tac.inspect_sigelt se with
    | Tac.Sg_Let {lbs} -> Tac.lookup_lb lbs nm
    | _ -> Tac.fail ("lookup_lb_top: binding is not a let-binding: " ^ Ref.implode_qn nm)

let term_check_fv (t: Tac.term) (fv: string): Tac.Tac bool =
  match Tac.inspect t with
  | Tac.Tv_FVar fv'
  | Tac.Tv_UInst fv' _ ->
    Tac.inspect_fv fv' = Tac.explode_qn fv
  | _ -> false

let rec is_compound_term (t: Tac.term): Tac.Tac bool =
  match Tac.inspect t with
  | Tac.Tv_Var _
  | Tac.Tv_BVar _
  | Tac.Tv_FVar _
  | Tac.Tv_UInst _ _
  | Tac.Tv_Type _
  | Tac.Tv_Const _
  | Tac.Tv_Uvar _ _
  | Tac.Tv_Unknown
  | Tac.Tv_Unsupp
  ->
    false
  | Tac.Tv_AscribedT e _ _ _
  | Tac.Tv_AscribedC e _ _ _ ->
    is_compound_term e

  | _ -> true


let rec collect_list (tm: Tac.term): Tac.Tac (list Tac.term) =
  let (hd,args) = Tac.collect_app tm in
  if term_check_fv hd (`%Prims.Nil)
  then []
  else if term_check_fv hd (`%Prims.Cons)
  then match args with
    | [ a, Tac.Q_Explicit; b, Tac.Q_Explicit ]
    | [ _, Tac.Q_Implicit; a, Tac.Q_Explicit; b, Tac.Q_Explicit ] ->
      a :: collect_list b
    | _ -> [tm]
  else []

let rec mk_list (tms: list Tac.term): Tac.Tac Tac.term =
  match tms with
  | [] -> `[]
  | a :: tms ->
    let tms = mk_list tms in
    `((`#a) :: (`#tms))
