open Fstarcompiler

module FI   = FStarC_Ident
module FC   = FStarC_Const

open FStarC_Parser_AST
open FStarC_Range

let fatal (r: range) (str: string) =
  failwith ("Pipit: fatal: " ^ str ^ " (" ^ string_of_range r ^ ")")

let mod_path = ["Pipit"; "Plugin"; "Interface"]
let src_lid i = FI.lid_of_path (mod_path @ [i])

(* let lid_stream = src_lid "stream" *)
let rec_lid = src_lid "rec'"
let lift_tac_lid = FI.lid_of_path ["Pipit"; "Plugin"; "Lift"; "lift_tac"]
let core_of_source_lid = src_lid "core_of_source"
let extract_lid = src_lid "extract"
let source_mode_lid = src_lid "source_mode"

let mStream_lid = src_lid "Stream"
let mStatic_lid = src_lid "Static"
let mModeFun_lid = src_lid "ModeFun"

let match_lid (f: range -> FI.lident) (i: FI.lident): bool =
  let ii = f dummyRange in
  FI.lid_equals i ii

type mode_fun_qualifier = bool
let mf'implicit = false
let mf'explicit = true
(* LODO don't need this, use generated from Pipit.Plugin.Interface? *)
type mode =
  | Stream
  | Static
  | ModeFun of (mode * mode_fun_qualifier * mode)

let rec quote_mode (m: mode) (range: range): term =
  let level = Expr in
  let tm = match m with
    | Stream -> Construct (mStream_lid range, [])
    | Static -> Construct (mStatic_lid range, [])
    | ModeFun (m,x,m') ->
      let x = { tm = Const (FC.Const_bool x); range; level } in
      Construct (mModeFun_lid range, [quote_mode m range, Nothing; x, Nothing; quote_mode m' range, Nothing])
  in
   { tm; range; level }

let rec unquote_mode (tm: term): mode =
  match tm.tm with
  | Construct (id, []) when match_lid mStream_lid id
    -> Stream
  | Construct (id, []) when match_lid mStatic_lid id
    -> Static
  | Construct (id, [m, Nothing; { tm = Const (FC.Const_bool x); _ }, Nothing; m', Nothing])
    when match_lid mModeFun_lid id
    -> ModeFun (unquote_mode m, x, unquote_mode m')

let quote_mode_attr (m: mode) (range: range): term =
  let level = Expr in
  let f = { tm = Name (source_mode_lid range); range; level } in
  { tm = App (f, quote_mode m range, Nothing); range; level = Expr }


let rec string_of_mode (m: mode): string =
  match m with
  | Stream -> "Stream"
  | Static -> "Static"
  | ModeFun (m,true,m') -> "(" ^ string_of_mode m ^ " -> " ^ string_of_mode m' ^ ")"
  | ModeFun (m,false,m') -> "(" ^ string_of_mode m ^ " #->" ^ string_of_mode m' ^ ")"

let rec mode_any_stream (m: mode): bool =
  match m with
  | Stream -> true
  | Static -> false
  | ModeFun (m,_,m') -> mode_any_stream m || mode_any_stream m'

let mode_qual_of_aqual (a: aqual) = match a with
  | Some _ -> mf'implicit
  | None   -> mf'explicit

let default_mode (m: mode option) = Option.value m ~default: Static


let mk_modefuns (ms: (mode * binder) list) (ty: term) ((md, mt): mode option * term): (mode * term') =
  let rec go_md ms = match ms with
    | [] -> default_mode md
    | (m,b) :: ms -> ModeFun (m, mode_qual_of_aqual b.aqual, go_md ms)
  in
  let prod_bs = List.map snd ms in
  go_md ms, Product (prod_bs, mt)

let rec mode_of_type (t: term): (mode option * term) =
  let nop = None, t in
  match t.tm with
  | Wild | Const _ | Op _ | Uvar _ | Name _ -> nop
  | Projector _ -> nop
  | Var lid ->
    if FI.string_of_lid lid = "stream"
    then fatal t.range "unapplied stream type"
    else nop
  | Construct (con,args) -> (* TODO descend args, assert None *)
    nop
  | Abs _ -> (* TODO descend, assert None *) nop
  | Function _ -> (* TODO descend, assert None *) nop

  | App ({ tm = Var ident ; _ }, ty, Nothing) ->
      if FI.string_of_lid ident = "stream"
      then Some Stream, ty
      else nop
  | App (f, ty, _) ->
    let _ = mode_of_type f in
    nop
  | Product (bs, ty) -> begin
    let ms = List.map (fun b ->
      let m, b = mode_of_binder b in
      default_mode m, b) bs in
    let m, ty = mk_modefuns ms ty (mode_of_type ty) in
    (Some m, { t with tm = ty })
  end

  | Paren p -> mode_of_type p

  | NamedTyp _ ->
    nop

  | _ ->
    nop

and
  mode_of_binder b = match b.b with
   | Variable _ -> None, b
   | Annotated (i, ty) ->
      let m, ty = mode_of_type ty in
      m, { b with b = Annotated (i, ty) }
   | NoName ty ->
      let m, ty = mode_of_type ty in
      m, { b with b = NoName ty }

let rec mode_of_pattern (p: pattern): (mode * bool * pattern) =
  match p.pat with
  | PatAscribed ({ pat = PatApp (phd, args); prange }, (ty, None)) ->
    let mhd, xhd, phd = mode_of_pattern phd in
    let ms = List.map mode_of_pattern args in
    let rmd, rty = mode_of_type ty in
    let rec mk_mode ms = match ms with
     | [] -> default_mode rmd
     | (m, x, p) :: ms ->
       ModeFun (m, x, mk_mode ms)
    in
    let mk_pat =
      PatAscribed ({ pat = PatApp (phd, List.map (fun (m,x,p) -> p) ms); prange }, (rty, None))
     in mk_mode ms, xhd, { pat = mk_pat; prange = p.prange }

  | PatAscribed (phd, (ty, None)) ->
    let mhd, xhd, phd = mode_of_pattern phd in
    let rmd, rty = mode_of_type ty in
    default_mode rmd, xhd, { pat = PatAscribed (phd, (rty, None)); prange = p.prange }

  | PatApp (phd, args) ->
    let mhd, xhd, phd = mode_of_pattern phd in
    let ms = List.map mode_of_pattern args in
    let rec mk_mode ms any_stream = match ms with
     | [] -> if any_stream then Stream else Static
     | (m, x, p) :: ms ->
       ModeFun (m, x, mk_mode ms (any_stream || m = Stream))
    in
    let mk_pat =
      PatApp (phd, List.map (fun (m,x,p) -> p) ms)
     in mk_mode ms false, xhd, { pat = mk_pat; prange = p.prange }

  | PatWild (None, _)
  | PatVar (_, None, _)
  -> Static, true, p
  | PatWild (Some _, _)
  | PatVar (_, Some _, _)
  -> Static, false, p

  | _ -> Static, true, p

let rec mode_of_term (t: term): mode option =
  match t.tm with
  | Wild | Const _ | Op _ | Uvar _ 
  | Var _ | Name _ | Projector _ | Construct _
  -> None
  | Abs (ps, body) ->
    let pss = List.map mode_of_pattern ps in
    (* TODO set default if any stream, TODO construct ModeFun *)
    let dflt = if List.exists (fun (m, _, _) -> mode_any_stream m) pss then Stream else Static in
    let m = Option.value (mode_of_term body) ~default:dflt in
    Some m
  | Function _ -> fatal t.range "TODO Function"
  | App _ -> None
  | Let _ -> None

  | Paren tm -> mode_of_term tm

  | Ascribed (_, ty, None, false) ->
    fst (mode_of_type ty)

  | LetOperator _ | LetOpen _ | LetOpenRecord _ -> None
  | Seq _ -> None
  | _ -> None

