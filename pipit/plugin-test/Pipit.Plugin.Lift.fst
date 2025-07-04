// TODO move this to plugin/
// TODO fix extraction for plugin
module Pipit.Plugin.Lift

open Pipit.Plugin.Interface

module Tac = FStar.Tactics.V2
module Ref = FStar.Reflection.V2

module PTB = Pipit.Tactics.Base

module Range = FStar.Range

module List = FStar.List.Tot

module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table
module PXB  = Pipit.Exp.Base
module PXBi  = Pipit.Exp.Binding

module PTC = Pipit.Tactics.Cse

module TermEq = FStar.Reflection.TermEq.Simple


let shallow_ty t = `PSSB.shallow (`#t)
let shallow_prim_mkPrim a b c = `PPS.mkPrim (`#a) (`#b) (`#c)

let table_FTFun a b = `(PPT.FTFun (`#a) (`#b))
let table_FTVal a = `(PPT.FTVal (`#a))

// LODO this should use checked expressions cexp instead of raw expressions.
//      but be careful not to slow down typechecking of generated expressions
// LODO not sure if ctx is useful - just use closed expressions
//  ...for checking expressions, they need to be closed - otherwise conversion to transition system gets stuck.
//  ...and contracts need to be sealed, so we can't substitute expressions into them with unproved checks
let exp_ty ctx a = `(PXB.exp PPS.table (`#ctx) (`#a))
let ctx_ty = `(PPT.context PPS.table)

// TODO should these take ctx?
let exp_XPrim' ctx a = `PXB.XPrim #(PPS.table) #(`#ctx) (`#a)
let exp_XPrim = exp_XPrim' (`_)
let exp_XApp3' ctx ty hd tl = `(PXB.XApp #(PPS.table) #(`#ctx) #(`#ty) (`#hd) (`#tl) )
let exp_XApp3 = exp_XApp3' (`_)
let exp_XApps2' ctx ty exp = `(PXB.XApps #(PPS.table) #(`#ctx) #(`#ty) (`#exp))
let exp_XApps2 = exp_XApps2' (`_)
let exp_XBVar v = `(PXB.XBase #(PPS.table) (PXB.XBVar #(PPS.table) (`#v)))
let exp_XVal v = `(PXB.XBase #(PPS.table) (PXB.XVal #(PPS.table) (`#v)))
let exp_XLet ty def body = `(PXB.XLet #(PPS.table) (`#ty) (`#def) (`#body))
let exp_XRec body = `(PXB.XMu #(PPS.table) (`#body))
let exp_lifts ctx pfx exp = `(PXBi.lifts #(PPS.table) #_ #(`#ctx) (`#exp) (`#pfx))
let exp_weaken ctx pfx exp = `(PXB.weaken #(PPS.table) #(`#ctx) (`#pfx) (`#exp))

// quote doesn't work with extraction (I think) so implement manually for modes
let rec quote_mode (m: mode): Tac.term =
  match m with
    | Stream -> `Stream
    | Static -> `Static
    | ModeFun m x m' ->
      let x = if x then `true else `false in
      `ModeFun (`#(quote_mode m)) (`#x) (`#(quote_mode m'))

// assuming Tac.unquote doesn't work for extraction?
let rec unquote_mode (tm: Tac.term): Tac.Tac mode =
  let err () = Tac.fail ("bad ModeFun: " ^ Tac.term_to_string tm) in
  match Tac.inspect tm with
  | Tac.Tv_FVar fv ->
    if Tac.inspect_fv fv = ["Pipit"; "Plugin"; "Interface"; "Stream"]
    then Stream
    else if Tac.inspect_fv fv = ["Pipit"; "Plugin"; "Interface"; "Static"]
    then Static
    else err ()
  | Tac.Tv_App hd (m', _) ->
    (match Tac.inspect hd with
    | Tac.Tv_App hd (x, _) ->
    (match Tac.inspect hd with
    | Tac.Tv_App hd (m, _) ->
    (match Tac.inspect hd with
    | Tac.Tv_FVar fv ->
    if Tac.inspect_fv fv = ["Pipit"; "Plugin"; "Interface"; "ModeFun"]
    then
    let x =
      match Tac.inspect x with
      | Tac.Tv_Const Tac.C_True -> true
      | Tac.Tv_Const Tac.C_False -> false
      | _ -> Tac.fail ("bad ModeFun: expected const bool, got " ^ Tac.term_to_string x)
    in
      ModeFun (unquote_mode m) x (unquote_mode m')
    else err ()
    | _ -> err ())
    | _ -> err ())
    | _ -> err ())
  | _ -> err ()


let debug_print (str: unit -> Tac.Tac string): Tac.Tac unit =
  if Tac.ext_getv "pipit:lift:debug" <> ""
  then (
    let ms = Tac.curms () in
    Tac.print ("[ppt-lift@" ^ string_of_int ms ^ "]: " ^ str ())
  )

let fail (#a: Type) (msg: string) (rng: Range.range) (ctx: list string): Tac.Tac a =
  let str0 = "Pipit: lift transform: failure at " ^ Tac.range_to_string rng ^ "\n  " ^ msg in
  let str = List.fold_left (fun str str' -> str ^ "\n    * " ^ str') str0 ctx in
  Tac.fail str

noeq
type bind_sort =
  | BindLocal of Tac.typ
  | BindMeta

noeq
type env = {
  // tactic superenvironment (invariant)
  tac_env: Tac.env;
  // for each local variable in scope, mapping from unique id to mode (lexical),
  // as well as whether it exists as a real meta-level binding or only on object-level
  mode_env: list (nat & mode & bind_sort);
  // mapping of lifted binding source to core ids (invariant)
  lifted_env: list (Ref.name & Ref.name & mode);
  // list of extra top-level bindings to add at end of lift (mutable)
  extra_sigelts: Tac.tref (list Tac.sigelt);
  // mapping of lifted primitives (mutable)
  prim_env: Tac.tref (list (Ref.name & Ref.name & mode));
  // cache for shallow stream type lookup
  shallow_cache: Tac.tref (list (Ref.name & Tac.term));
  // name of top-level binding we're lifting (invariant)
  name_prefix: string;
  // context variable (invariant)
  ctx_uniq: Tac.namedv;
}

(* construct top-level binding for given term *)
let core_sigelt (e: env) (attrs: list Tac.term) (nm_src nm_core: option string) (m: mode) (tm: Tac.term): Tac.Tac (Tac.name & Tac.sigelt) =
  let nm_def = match nm_core, nm_src with
    | Some n, _ -> Ref.explode_qn n
    | None, Some n ->
      (match List.rev (Ref.explode_qn n) with
      | x :: _ ->
        let open List in
        let u = Tac.fresh () in
        let m = Tac.cur_module () in
        m @ ["__prim_" ^ x ^ string_of_int u]
      | _ ->
      let u = Tac.fresh () in
      Ref.explode_qn (e.name_prefix ^ "__prim_" ^ string_of_int u))
    | _ ->
      let u = Tac.fresh () in
      Ref.explode_qn (e.name_prefix ^ "__prim_" ^ string_of_int u)
  in

  let ty = Tac.pack Tac.Tv_Unknown in
  // TODO: support recursive bindings
  // pack multiple bindings into one sigelt
  // set isrec to true if rec
  let lb_core: Tac.letbinding = {
    lb_fv  = Tac.pack_fv nm_def;
    lb_us  = [];
    lb_typ = ty;
    lb_def = tm;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let {isrec=false; lbs=[lb_core]} in
  let se: Tac.sigelt = Tac.pack_sigelt sv in
  let attrs = match nm_src with
    | Some nm -> (`core_of_source (`#(Tac.pack (Tac.Tv_Const (Ref.C_String nm)))) (`#(quote_mode m))) :: attrs
    | None -> attrs in
  debug_print (fun () -> "core_sigelt: " ^ Ref.implode_qn nm_def);
  debug_print (fun () -> "core_sigelt: " ^ Tac.term_to_string tm);
  nm_def, Ref.set_sigelt_attrs attrs se

(* construct mapping from source to lifted core for given top-level binding *)
let env_lifted_mapping (tac_env: Tac.env) (lift_fv: Ref.fv): Tac.Tac (option (Ref.name & Ref.name & mode)) =
  let lift_nm = Tac.inspect_fv lift_fv in
  let lift_se = Tac.lookup_typ tac_env lift_nm in
  let rec go (attrs: list Tac.term): Tac.Tac (option (Ref.name & Ref.name & mode)) =
    match attrs with
    | [] -> None
    | hd :: tl ->
      let (hd,args) = Tac.collect_app hd in
      if PTB.term_check_fv hd (`%core_of_source)
      then (match args with
        | [(arg,_); (mode,_)] ->
          (match Tac.inspect arg with
          | Tac.Tv_Const (Ref.C_String nm) -> Some (lift_nm, Tac.explode_qn nm, unquote_mode mode)
          | _ -> fail
            ("cannot parse attribute " ^ Tac.term_to_string hd)
            (Tac.range_of_term arg)
            ["in binding " ^ Ref.implode_qn lift_nm])
        | _ -> go tl)
      else go tl
  in
  match lift_se with
  | Some se ->
    let attrs = Ref.sigelt_attrs se in
    go attrs
  | None -> None

let env_core_nm (nm: string): string =
  nm ^ "_core"

(* construct environment for transform *)
let env_top (tac_env: Tac.env) (extra_lifteds: list (Ref.name & Ref.name & mode)) (name_prefix: string): Tac.Tac env =
  let mode_env = [] in
  let lifts = Ref.lookup_attr (`core_lifted) tac_env in
  let prims = Ref.lookup_attr (`core_lifted_prim) tac_env in
  let lifted_env = Tac.filter_map (env_lifted_mapping tac_env) lifts in
  let lifted_env = List.(lifted_env @ extra_lifteds) in
  let prim_env = Tac.filter_map (env_lifted_mapping tac_env) prims in
  let prim_env = Tac.alloc prim_env in
  let extra_sigelts = Tac.alloc [] in
  let ctx_uniq: Tac.namedv = { uniq = Tac.fresh (); sort = Tac.seal ctx_ty; ppname = Ref.as_ppname "ctx" } in
  let shallow_cache = Tac.alloc [] in
  { tac_env; mode_env; lifted_env; prim_env; extra_sigelts; name_prefix; ctx_uniq; shallow_cache }

let env_nil (nms: list (string & mode)): Tac.Tac env =
  let prefix = match nms with
    | [] -> "_autolift_default_"
    | (nm, m) :: _ -> nm
  in
  let extras = List.map (fun (nm,m) -> (Tac.explode_qn (env_core_nm nm), Tac.explode_qn nm, m)) nms in
  env_top (Tac.top_env ()) extras prefix

let env_push (b: Tac.binder) (m: mode) (bs: bind_sort) (e: env): env =
  { e with
    tac_env  = Ref.push_namedv e.tac_env (Ref.pack_namedv b);
    mode_env = (b.uniq, m, bs) :: e.mode_env;
  }

let env_push_bs (m: mode) (bs: bind_sort) (e: env): Tac.Tac env =
  let u = Tac.fresh () in
  { e with
    mode_env = (u, m, bs) :: e.mode_env;
  }

(* Get mode (stream / non-stream) of local binding. We also get the de bruijn
  index of the stream bindings *)
let env_get_mode (b: Tac.namedv) (e: env) (rng: Range.range): Tac.Tac (mode & nat & bind_sort) =
  let rec go (bs: list (nat & mode & bind_sort)) (strm_ix: nat): Tac.Tac (mode & nat & bind_sort) =
    match bs with
    | [] ->
      fail ("no such binder: b" ^ Tac.unseal b.ppname)
        rng
        ["(internal error)"]
    | (uniq, m, bind_sort) :: bs ->
      if uniq = b.uniq
      then (m, strm_ix, bind_sort)
      else if m = Stream
      then go bs (strm_ix + 1)
      else go bs strm_ix
  in go e.mode_env 0

let rec env_push_pat (p: Tac.pattern) (m: mode) (bs: bind_sort) (e: env): Tac.Tac env =
  match p with
  | Tac.Pat_Constant _ -> e
  | Tac.Pat_Cons c ->
    Tac.fold_left (fun e (p,_) -> env_push_pat p m bs e) e c.subpats
  | Tac.Pat_Var v ->
    env_push (Tac.namedv_to_binder v.v (Tac.unseal v.sort)) m bs e
  | Tac.Pat_Dot_Term _ -> e

let env_lifted_lookup (fv: Ref.fv) (lifts: list (Tac.name & Tac.name & mode)): Tac.Tac (option (Ref.fv & mode)) =
  let nm = Tac.inspect_fv fv in
  let rec go (bs: list (Ref.name & Ref.name & mode)): Tac.Tac (option (Ref.fv & mode)) =
    match bs with
    | [] -> None
    | (lifted,src,m) :: tl ->
      if nm = src
      then Some (Tac.pack_fv lifted, m)
      else go tl
  in go lifts

let env_get_lifted_of_source (fv: Ref.fv) (e: env): Tac.Tac (option (Ref.fv & mode)) =
  env_lifted_lookup fv e.lifted_env

let get_exp_context (tm: Tac.term) (e: env): Tac.Tac (list Tac.typ & Tac.typ) =
    let ty = Tac.tc e.tac_env tm in
    let (_, ret) = Tac.collect_arr ty in
    match ret with
    | Tac.C_Total e
    | Tac.C_GTotal e
    | Tac.C_Eff _ _ e _ _ ->
    // assert hd = exp
      let (hd, args) = Tac.collect_app e in
      (match args with
      | [_; ctx, Ref.Q_Explicit; ret, Ref.Q_Explicit] ->
        (PTB.collect_list ctx, ret)
      | _ ->
        fail "get_exp_context"
          (Tac.range_of_term tm)
          ["tm:"; Tac.term_to_string tm; "ty:"; Tac.term_to_string ty])
    | _ ->
        fail "get_exp_context"
          (Tac.range_of_term tm)
          ["tm:"; Tac.term_to_string tm; "ty:"; Tac.term_to_string ty]


let env_get_lifted_prim_of_source (fv: Ref.fv) (e: env): Tac.Tac (option (Ref.fv & mode)) =
  env_lifted_lookup fv (Tac.read e.prim_env)

let rec tm_shallow_can_cache (t: Tac.term): Tac.Tac bool =
  match Tac.inspect t with
  | Tac.Tv_Var _ | Tac.Tv_BVar _
  -> false
  | Tac.Tv_App hd (arg,_)
  -> if tm_shallow_can_cache hd
     then false
     else tm_shallow_can_cache arg
  | Tac.Tv_Abs _ _
  | Tac.Tv_Arrow _ _
  | Tac.Tv_Refine _ _
  | Tac.Tv_Let _ _ _ _ _
  | Tac.Tv_Match _ _ _
  | Tac.Tv_AscribedT _ _ _ _
  | Tac.Tv_AscribedC _ _ _ _
   -> false

  | _ -> true

let rec env_get_shallow_ty_search (ls: list (Tac.name & Tac.term)) (t: Tac.term) (e: env): Tac.Tac Tac.term =
  match ls with
  | [] ->
    let (nm, se) = core_sigelt e [] None None Static (shallow_ty t) in
    let sh = Tac.read e.shallow_cache in
    Tac.write e.shallow_cache ((nm, t) :: sh);
    Tac.write e.extra_sigelts (se :: Tac.read e.extra_sigelts);
    Tac.pack (Tac.Tv_FVar (Tac.pack_fv nm))
  | (nm, t') :: ls ->
    if TermEq.term_eq t t'
    then Tac.pack (Tac.Tv_FVar (Tac.pack_fv nm))
    else env_get_shallow_ty_search ls t e


let env_get_shallow_ty (t: Tac.term) (e: env): Tac.Tac Tac.term =
  if tm_shallow_can_cache t
  then
    let sh = Tac.read e.shallow_cache in
    env_get_shallow_ty_search sh t e
  else shallow_ty t

let env_get_abstract_context (e: env): Tac.term =
  Tac.pack (Tac.Tv_Var e.ctx_uniq)

let env_get_full_context (e: env): Tac.Tac Tac.term =
  let rec go (l: list (nat & mode & bind_sort)): Tac.Tac Tac.term =
    match l with
    | [] -> `[]
    | (n, m, BindLocal ty) :: ms -> `((`#(ty)) :: (`#(go ms)))
    | _ :: ms -> go ms
  in
    go e.mode_env

// let env_lifts (e: env) (t: Tac.term): Tac.Tac Tac.term =
//   let rec go (l: list (nat & mode & bind_sort)): Tac.Tac Tac.term =
//     match l with
//     | [] -> `[]
//     | (n, m, BindLocal ty) :: ms -> `((`#(env_get_shallow_ty ty e)) :: (`#(go ms)))
//     | _ :: ms -> go ms
//   in
//     let pfx = go e.mode_env in
//     if TermEq.term_eq pfx (`[])
//     then t
//     else exp_lifts (Tac.pack (Tac.Tv_Var e.ctx_uniq)) pfx t

let env_weaken_get_prefix (e: env): Tac.Tac Tac.term =
  let rec go (l: list (nat & mode & bind_sort)): Tac.Tac Tac.term =
    match l with
    | [] -> `[]
    | (n, m, BindLocal ty) :: ms -> `((`#(ty)) :: (`#(go ms)))
    | _ :: ms -> go ms
  in
    go e.mode_env

let env_weaken (e: env) (t: Tac.term): Tac.Tac Tac.term =
    let pfx = env_weaken_get_prefix e in
    if TermEq.term_eq pfx (`[])
    then t
    // TODO give explicit context?
    else exp_weaken (Tac.pack Tac.Tv_Unknown) pfx t

let rec mode_of_attrs (attrs: list Tac.term): Tac.Tac (option mode) =
  match attrs with
  | [] -> None
  | hd :: tl ->
    let (hd,args) = Tac.collect_app hd in
    if PTB.term_check_fv hd (`%source_mode)
    then (match args with
      | [(mode,_)] ->
        Some (unquote_mode mode)
      | _ -> fail
            ("cannot parse attribute " ^ Tac.term_to_string hd)
            (Tac.range_of_term hd)
            [])
    else mode_of_attrs tl

let rec mode_of_ty_pure (ty: Tac.term): Tac.Tac mode =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_Arrow arg (Tac.C_Total res)
  | Tac.Tv_Arrow arg (Tac.C_GTotal res)
  // We don't support general effects, but parse them anyway in case the effect is Tot
  | Tac.Tv_Arrow arg (Tac.C_Eff _ _ res _ _) ->
    ModeFun (mode_of_ty_pure arg.sort) (PTB.qual_is_explicit arg.qual) (mode_of_ty_pure res)
  | Tac.Tv_Arrow arg (Tac.C_Lemma _ _ _) ->
    ModeFun (mode_of_ty_pure arg.sort) (PTB.qual_is_explicit arg.qual) Static
  | t ->
    Static

let mode_join (rng: Range.range) (m1 m2: mode): Tac.Tac mode = match m1, m2 with
  | Stream, Static -> Stream
  | Static, Stream -> Stream
  | Static, Static -> Static
  | _, _ -> if m1 = m2 then m1 else fail ("cannot join incompatible modes: " ^ Tac.term_to_string (quote (m1, m2))) rng []

let mode_cast (m_expect: mode) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  (match mt, m_expect with
  | (Static, tm), Stream -> (Stream, exp_XVal tm)
  | (m, tm), _ -> (m, tm))

let mode_cast_opt (rng: Range.range) (m_expect: option mode) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  (match mt, m_expect with
  | (Static, tm), Some Stream -> (Stream, exp_XVal tm)
  | (m, tm), Some m' ->
    let _ = mode_join rng m m' in
    (m, tm)
  | (m, tm), None -> (m, tm))


let rec lift_mode (m: mode): mode =
  match m with
  | Static -> Stream
  | Stream -> Stream
  // XXX check that function does not contain any streams already, must be pure
  | ModeFun m1 e m2 -> ModeFun Stream e (lift_mode m2)

let joins_modes (rng: Range.range) (mts: list (mode & Tac.term)): Tac.Tac (mode & list Tac.term) =
  match mts with
  | (m0, tm) :: mts' ->
    let ms' = List.map fst mts' in
    let m = Tac.fold_left (mode_join rng) m0 ms' in
    (m, Tac.map (fun x -> snd (mode_cast m x)) mts)
  | [] -> (Static, [])


(* Strip refinements out of types *)
let strip_ty_visit (t: Tac.term): Tac.Tac Tac.term =
  match Tac.inspect t with
  | Tac.Tv_Refine b r -> b.sort
  | _ -> t

let strip_ty: Tac.term -> Tac.Tac Tac.term =
  Tac.visit_tm strip_ty_visit

// TODO merge lift_prim_gen,lift_prim_gen_apply
let lift_prim_gen_apply (e: env) (prim: Tac.term) (args: list (Tac.term & Tac.typ)) (tret: Tac.typ): Tac.Tac Tac.term =
  let nm =
    match Tac.inspect_unascribe prim with
    | Tac.Tv_FVar fv ->
      let fv' = Tac.inspect_fv fv in
      Some (Ref.implode_qn fv')
    | _ -> Some (e.name_prefix ^ "__prim_anon_" ^ string_of_int (Tac.fresh ()))
  in
  let nm_tm =
    match nm with
    | Some f -> (quote (Some f))
    | None -> (`None)
  in
  let ft =
    Tac.fold_right (fun (_,a) b -> table_FTFun (env_get_shallow_ty a e) b) args (table_FTVal (env_get_shallow_ty tret e))
  in
  let prim = (exp_XPrim (shallow_prim_mkPrim nm_tm ft prim)) in
  let lift = Tac.fold_left
    (fun hd (arg,ty) ->
      exp_XApp3 (env_get_shallow_ty ty e) hd arg)
    prim args
  in
  let lift = exp_XApps2 (env_get_shallow_ty tret e) lift in
  lift

let lift_prim_gen (e: env) (prim: Tac.term): Tac.Tac Tac.term =
  let ty = strip_ty (PTB.tc_unascribe e.tac_env prim) in
  let nm =
    match Tac.inspect_unascribe prim with
    | Tac.Tv_FVar fv ->
      let fv' = Tac.inspect_fv fv in
      Some (Ref.implode_qn fv')
    | _ -> Some (e.name_prefix ^ "__prim_anon_" ^ string_of_int (Tac.fresh ()))
  in
  let nm_tm =
    match nm with
    | Some f -> (quote (Some f))
    | None -> (`None)
  in
  let (args,res) = Tac.collect_arr ty in
  let res = PTB.returns_of_comp res in
  let ft =
    Tac.fold_right (fun a b -> table_FTFun (env_get_shallow_ty a e) b) args (table_FTVal (env_get_shallow_ty res e))
  in
  let ctx = Tac.pack (Tac.Tv_Var e.ctx_uniq) in
  let argnamedvs = Tac.map
    (fun ty ->
      let tys = exp_ty ctx (env_get_shallow_ty ty e) in
      ty, ({ uniq = Tac.fresh (); sort = Tac.seal tys; ppname = Ref.as_ppname "prim" } <: Tac.namedv))
    args
  in
  // eta expand primitives, if necessary: this is necessary for treating lemmas as unit prims.
  // it also helps deal with an old, now-fixed, bug in F* normaliser where un-eta'd primops got bad types.
  // for some reason, properties don't seem to verify without this
  let prim = match Tac.inspect_unascribe prim with
    | Tac.Tv_Abs _ _ -> prim
    | _ -> PTB.eta_expand prim ty
  in
  let prim = (exp_XPrim' ctx (shallow_prim_mkPrim nm_tm ft prim)) in
  // TODO: deal with implicit args
  let lift = Tac.fold_left
    (fun hd (ty,nv) ->
      let tm = Tac.pack (Tac.Tv_Var nv) in
      exp_XApp3' ctx (env_get_shallow_ty ty e) hd tm)
    prim argnamedvs
  in
  let lift = exp_XApps2' ctx (env_get_shallow_ty res e) lift in
  let abs = Tac.fold_right
    (fun (ty,nv) hd ->
      let tys = exp_ty ctx (env_get_shallow_ty ty e) in
      Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder nv tys) hd))
    argnamedvs lift
  in
  let abs_ctx = Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder e.ctx_uniq ctx_ty) abs) in
  abs_ctx

let lift_prim (e: env) (prim: Tac.term) (m: mode): Tac.Tac Tac.term =
  match Tac.inspect prim with
  | Tac.Tv_FVar fv ->
    (match env_get_lifted_prim_of_source fv e with
    | Some (fv',m) ->
      Tac.pack (Tac.Tv_FVar fv')
    | None ->
      let nm = Tac.inspect_fv fv in
      let prim = lift_prim_gen e prim in
      let nm_def, sigelt = core_sigelt e [`core_lifted_prim] (Some (Tac.implode_qn nm)) None m prim in
      Tac.write e.prim_env ((nm_def, nm, m) :: Tac.read e.prim_env);
      Tac.write e.extra_sigelts (sigelt :: Tac.read e.extra_sigelts);
      (Tac.pack (Tac.Tv_FVar (Tac.pack_fv nm_def))))
  | _ -> lift_prim_gen e prim

let lift_stream_match (e: env) (tscrut: Tac.term) (tret: Tac.term) (scrut: Tac.term) (ret: option Tac.match_returns_ascription) (brs: list (Tac.pattern & (mode & Tac.term))): Tac.Tac Tac.term =
  let mk_namedv (pp: string) (ty: Tac.term) =
    { uniq = Tac.fresh (); sort = Tac.seal ty; ppname = Ref.as_ppname pp } <: Tac.namedv
  in
  let nscrut = mk_namedv "scrut" tscrut in
  let nbrs = Tac.map (fun (pat,(m,tm)) ->
    (mk_namedv "branch" tret, pat, tm)) brs in
  let brs = List.map (fun (nm,pat,tm) -> (pat, Tac.pack (Tac.Tv_Var nm))) nbrs in
  let xmatch = Tac.pack (Tac.Tv_Match (Tac.pack (Tac.Tv_Var nscrut)) ret brs) in
  let rec go_abs hd nms: Tac.Tac Tac.term = match nms with
    | [] -> hd
    | (nm,ty)::nms ->
      go_abs (Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder nm ty) hd)) nms
  in
  let abs = go_abs xmatch (List.rev ((nscrut, tscrut) :: List.map (fun (nm,_,_) -> (nm, tret)) nbrs)) in
  let args = (scrut, tscrut) :: List.map (fun (_,_,tm) -> (tm, tret)) nbrs in
  let p = lift_prim_gen_apply e abs args tret in
  p

let lift_ty (t: Tac.term) (m: mode) (e: env): Tac.Tac Tac.term =
  let t = strip_ty t in
  match m with
  | Stream ->
    let ctx = env_get_full_context e in
    exp_ty ctx (env_get_shallow_ty t e)
  | _ -> t

let strip_ty_simple_binder_static (b: Tac.simple_binder): Tac.Tac Tac.simple_binder =
  let sort = strip_ty b.sort in
  { b with sort = sort }

let rec mk_apps (proj: Tac.term) (args: list Tac.argv): Tac.Tac Tac.term =
  match args with
  | [] -> proj
  | arg :: args -> mk_apps (Tac.pack (Tac.Tv_App proj arg)) args

let mk_proj (scrut: Tac.term) (tscrut: Tac.term) (pat_head: Tac.name) (arrb: Tac.binder): Tac.Tac Tac.term =
  let proj_fv = match List.rev pat_head with
    | x :: xs -> Tac.pack_fv List.(rev xs @ ["__proj__" ^ x ^ "__item__" ^ Tac.unseal arrb.ppname])
    | [] -> Tac.fail "impossible: empty Pat_Cons, no constructor"
  in
  let proj = Tac.pack (Tac.Tv_FVar proj_fv) in
  // take type's parameters as implicit arguments to projector - questionable
  // TODO check that tscrut matches projector return type, might be a type synonym
  let (_tm, args) = Tac.collect_app tscrut in
  let args = List.map (fun (t,_) -> (t,Tac.Q_Implicit)) args in
  let proj = mk_apps proj List.(args @ [scrut, Tac.Q_Explicit]) in
  proj

let rec irrefutable_pats (e: env) (scrut: Tac.term) (tscrut: Tac.term) (pat_head: Tac.name) (pat_vars: list (Tac.pattern & bool)) (tm: Tac.term) (ty: Tac.term): Tac.Tac Tac.term =
  match pat_vars, Tac.inspect ty with
  | [], _ -> tm
  | (Tac.Pat_Dot_Term _, _) :: pat_vars', _ ->
     irrefutable_pats e scrut tscrut pat_head pat_vars' tm ty
  | (Tac.Pat_Var v, patq) :: pat_vars', Tac.Tv_Arrow b (Tac.C_Total ty')
   -> begin
   debug_print (fun () -> "irrefutable_pats: " ^ Tac.term_to_string (quote (patq, b.qual)));
    match patq, b.qual with
     | false, Tac.Q_Explicit
     | true, Tac.Q_Implicit
     | true, Tac.Q_Equality
     | true, Tac.Q_Meta _ ->
      let tm = irrefutable_pats e scrut tscrut pat_head pat_vars' tm ty' in
      let letb: Tac.simple_binder = { ppname = v.v.ppname; attrs = []; qual = Tac.Q_Explicit; sort = Tac.unseal v.sort; uniq = v.v.uniq; } in
      let def = mk_proj scrut tscrut pat_head b in
      Tac.pack (Tac.Tv_Let false [] letb def tm)
     | _ -> irrefutable_pats e scrut tscrut pat_head pat_vars tm ty'
    end
  // impossible?
  | _ ->
    fail "irrefutable_pats: unsupported pattern match"
      (Tac.range_of_term scrut)
      []


let rec lift_tm (e: env) (t: Tac.term) (mm: option mode): Tac.Tac (mode & Tac.term) =
  let ti = Tac.inspect t in
  let rng = Tac.range_of_term t in
  let go_mode = mode_cast_opt rng mm in
  match Tac.inspect t with
  | Tac.Tv_Var (v: Tac.namedv) ->
    let m, ix, bs = env_get_mode v e (Ref.range_of_term t) in
    go_mode
      (match m, bs with
      | Stream, BindLocal ty -> m, exp_XBVar (Tac.pack (Tac.Tv_Const (Tac.C_Int ix)))
      | Stream, BindMeta -> fail "Tv_Var: impossible (Stream,BindMeta)" rng []
      | _ -> m, t)
  | Tac.Tv_BVar (v: Tac.bv) ->
    fail
      ("unexpected bvar; expected named variables only " ^ Tac.term_to_string t)
      (Ref.range_of_term t) []
  | Tac.Tv_FVar _ | Tac.Tv_UInst _ _ ->
  // xxx strip_ty_visit necessary ???
  // TODO check if lifted, error on unapplied functions?
    let ty = PTB.tc_unascribe e.tac_env t in
    let m  = mode_of_ty_pure ty in
    go_mode (m, t)
  | Tac.Tv_Const (vc: Tac.vconst) ->
    go_mode (Static, t)

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let rec go_apps m hd args e: Tac.Tac (mode & Tac.term) = match m, args with
      | ModeFun _ false m2, (_,Ref.Q_Explicit)::_ ->
        go_apps m2 hd args e
      | ModeFun _ true m2, (_,Ref.Q_Implicit)::_ ->
        fail "unexpected implicit argument"
          (Ref.range_of_term arg)
          ["go_apps";
          "arg: " ^ Tac.term_to_string arg;
          "head: " ^ Tac.term_to_string hd;
          "mode: " ^ Tac.term_to_string (quote_mode m)]

      | ModeFun m1 mq m2, (arg0,aq)::args ->
        let (ma, arg) = lift_tm e arg0 (Some m1) in
        debug_print (fun () -> "go_apps: arg: " ^ Tac.term_to_string (quote ma) ^ " : " ^ Tac.term_to_string arg);
        (match ma, m1 with
        | Stream, Static ->
          (match aq with
          | Ref.Q_Explicit -> ()
          | _ ->
            fail "cannot lift implicit arguments - put all implicit arguments before explicits, or rearrange the arguments with a lambda (TODO)."
              (Ref.range_of_term arg)
              ["go_apps"]
            );
          let prim = lift_prim e hd m in
          let ctx_full = env_get_full_context e in
          let prim = `(`#prim) (`#ctx_full) in
          // TODO require m2 static
          let m2 = lift_mode m2 in
          go_apps m2 (Tac.pack (Tac.Tv_App prim (arg, aq))) args e
        | _, _ ->
          let (ma, arg) = mode_cast m1 (ma, arg) in
          go_apps m2 (Tac.pack (Tac.Tv_App hd (arg, aq))) args e)

      | _, (arg,_) :: _ ->
        fail "too many arguments for mode"
          (Ref.range_of_term arg)
          ["go_apps";
          "arg: " ^ Tac.term_to_string arg;
          "head: " ^ Tac.term_to_string hd;
          "mode: " ^ Tac.term_to_string (quote_mode m)]
      | _, [] -> (m, hd)
    in
    let (hd, args) = Tac.collect_app t in
    let (mh, hd) = lift_tm e hd None in
    let lifted_apps =
      match Tac.inspect hd with
      | Tac.Tv_FVar fv ->
        env_get_lifted_of_source fv e
      | _ -> None
    in
    begin
    match lifted_apps with
    | Some (hd,mh) ->
      lift_tm_lifted_apps e (Tac.pack (Tac.Tv_FVar hd)) args mh (env_weaken_get_prefix e) []
    | None ->
      if PTB.term_check_fv hd (`%rec')
      then match args with
        | [arg, Ref.Q_Explicit]
        | [_, Ref.Q_Implicit; arg, Ref.Q_Explicit] ->
          let abs_bv, abs_tm =
            match Tac.inspect arg with
            | Tac.Tv_Abs bv tm -> bv, tm
            | _ -> Tac.fail "bad rec', need abs"
          in
          let b = BindLocal (env_get_shallow_ty (abs_bv <: Tac.binder).sort e) in
          let m, t = lift_tm (env_push abs_bv Stream b e) abs_tm (Some Stream) in
          m, exp_XRec t

        | _ -> fail "rec': impossible: expected application" (Ref.range_of_term t) ["term: " ^ Tac.term_to_string t; "args: " ^ Tac.term_to_string (quote args)]
      else
        go_mode (go_apps mh hd args e)
    end

  | Tac.Tv_Abs bv tm ->
    debug_print (fun () -> "Abs: lift_tm with " ^ Tac.term_to_string bv.sort ^ "; mode " ^ Tac.term_to_string (quote mm));
    (match mm with
    | Some (ModeFun Stream mx m2) ->
      let bs = BindLocal (env_get_shallow_ty bv.sort e) in
      let (m2, tm) = lift_tm (env_push bv Stream bs e) tm (Some m2) in
      (ModeFun Stream (PTB.qual_is_explicit bv.qual) m2, tm)
    | Some (ModeFun m1 mx m2) ->
      let bs = BindMeta in
      let (m2, tm) = lift_tm (env_push bv m1 bs e) tm (Some m2) in
      let tm = Tac.pack (Tac.Tv_Abs bv tm) in
      (ModeFun m1 (PTB.qual_is_explicit bv.qual) m2, tm)
    | Some mm ->
      fail "bad mode for abstraction"
        (Ref.range_of_term tm)
        [ "expected mode: " ^ Tac.term_to_string (quote_mode mm)]
    | None ->
    // no mode qualifier on abs, so leave it as static
      debug_print (fun () -> "Abs: lift_tm with no mode, assume static");
      (Static, t))

  | Tac.Tv_Let true attrs b def body ->
    // LODO letrecs -- assume they won't have any streams in them for now.
    // recursive streams have been rewritten to calls to rec' by frontend
    let def_mode = mode_of_attrs attrs in
    go_mode (Static, t)
  | Tac.Tv_Let false attrs b def body ->
    let def_mode = mode_of_attrs attrs in
    let (md, def) = lift_tm e def def_mode in
    let bs = match md with
      | Stream -> BindLocal (env_get_shallow_ty b.sort e)
      | _ -> BindMeta in
    let (mb, body) = lift_tm (env_push b md bs e) body mm in
    let lett = match md, mb with
      | Stream, Stream ->
        exp_XLet (env_get_shallow_ty b.sort e) def body
      | _, _ ->
        let b = strip_ty_simple_binder_static b in
        Tac.pack (Tac.Tv_Let false attrs b def body)
    in
    (mb, lett)

  | Tac.Tv_Match scrut0 ret brs0 ->
    // LODO: lift_tm on ret
    let (ms, scrut) = lift_tm e scrut0 None in
    (match ms, brs0 with
    | Static, _ ->
      debug_print (fun () -> "match: static scrutinee " ^ Tac.term_to_string scrut);
      let mts = Tac.map (fun (pat,tm) -> lift_tm (env_push_pat pat Static BindMeta e) tm mm) brs0 in
      let (mbrs, ts) = joins_modes (Ref.range_of_term t) mts in
      let brs = Pipit.List.zip2 (List.map fst brs0) ts in
      (mbrs, Tac.pack (Tac.Tv_Match scrut ret brs))
    | Stream, [Tac.Pat_Cons c, tm] ->
      debug_print (fun () -> "match: irrefutable, stream scrutinee " ^ Tac.term_to_string scrut0);
      let ty = Tac.tc e.tac_env (Tac.pack (Tac.Tv_FVar c.head)) in
      // todo let-bind scrut to avoid duplication
      let tscrut = PTB.tc_unascribe e.tac_env scrut0 in
      let tm = irrefutable_pats e scrut0 tscrut (Tac.inspect_fv c.head) c.subpats tm ty in
      lift_tm e tm None

    | Stream, _ ->
      debug_print (fun () -> "match: stream scrutinee " ^ Tac.term_to_string scrut);
      // XXX: the current semantics for streaming-matches is more of a "select"
      // than a match: all of the branches are eagerly evaluated, and then we
      // just choose which to return based on the scrutinee
      let rec check_pat p: Tac.Tac unit = match p with
        | Tac.Pat_Constant _ -> ()
        | Tac.Pat_Cons c -> Tac.iter (fun (p,_) -> check_pat p) c.subpats
        | Tac.Pat_Var p ->
          // XXX hack assert variable not mentioned
          if Tac.unseal p.v.ppname <> "uu___"
          then
            fail ("streaming patterns can't bind variables (TODO)")
              (Ref.range_of_term t) ["in pattern-match"; "variable: " ^ Tac.unseal p.v.ppname]
        // not sure what this means...
        | Tac.Pat_Dot_Term _ -> ()
      in
      let brs = Tac.map (fun (pat,tm) -> check_pat pat; (pat, lift_tm e tm (Some Stream))) brs0 in

      // XXX: WRONG COMPLEXITY: this typechecking must be very bad for nested pattern matches - front-end preprocessor should insert type annotations
      let tscrut = PTB.tc_unascribe e.tac_env scrut0 in
      let tret = match brs0 with
       | (_, tm) :: _ ->
        PTB.tc_unascribe e.tac_env tm
       | [] -> Tac.pack Tac.Tv_Unknown in
      (Stream, lift_stream_match e tscrut tret scrut ret brs)
    | ModeFun _ _ _, _ ->
      fail "match scrutinee cannot be function"
        (Ref.range_of_term scrut) ["in pattern match"])

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    debug_print (fun () -> "AscribedT: " ^ Tac.term_to_string ty);
    let (mm, tm) = lift_tm e tm mm in
    (mm, Tac.pack (Tac.Tv_AscribedT tm (lift_ty ty mm e) tac use_eq))

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    (match cmp with
    | Tac.C_Total ty ->
      debug_print (fun () -> "AscribedC: " ^ Tac.term_to_string ty);
      let (mm, tm) = lift_tm e tm mm in
      (mm, Tac.pack (Tac.Tv_AscribedC tm (Tac.C_Total (lift_ty ty mm e)) tac use_eq))
      // TODO lemmas etc?
    | _ ->
      fail ("unsupported: type ascriptions on effects: " ^ Tac.comp_to_string cmp)
        (Ref.range_of_term t) [])

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ | Tac.Tv_Arrow  _ _ | Tac.Tv_Type   _
  | Tac.Tv_Refine _ _ | Tac.Tv_Unknown     -> go_mode (Static, strip_ty t)

  | Tac.Tv_Unsupp ->
    fail ("lift failed: cannot inspect term: " ^ Tac.term_to_string t)
      (Ref.range_of_term t) ["(unsupported term)"]

and lift_tm_lifted_apps (e: env) (hd: Tac.term) (args: list Tac.argv) (m: mode) (ctx0: Tac.term) (strm_apps: list Tac.term): Tac.Tac (mode & Tac.term) =
  match m, args with
  | ModeFun _ false m2, (_, Ref.Q_Explicit) :: _ ->
    lift_tm_lifted_apps e hd args m2 ctx0 strm_apps
  | ModeFun _ true m2, (_,Ref.Q_Implicit)::_ ->
    fail "unexpected implicit argument" (Ref.range_of_term hd)
      ["lift_tm_lifted_apps";
      "hd: " ^ Tac.term_to_string hd;
      "mode: " ^ Tac.term_to_string (quote_mode m)]

  | ModeFun Stream mq m2, (arg0,aq)::args ->
    let (ma, arg) = lift_tm e arg0 (Some Stream) in
    debug_print (fun () -> "lift_tm_lifted_apps: arg: " ^ Tac.term_to_string (quote ma) ^ " : " ^ Tac.term_to_string arg);
    let (ma, arg) = mode_cast Stream (ma, arg) in
    let b = BindLocal (`_) in
    let (mm, tm) = lift_tm_lifted_apps (env_push_bs Stream b e) hd args m2 ctx0 (arg :: strm_apps) in
    (mm, tm)

// TODO m1=ModeFun
  | ModeFun m1 mq m2, (arg0,aq)::args ->
    let (ma, arg) = lift_tm e arg0 (Some m1) in
    debug_print (fun () -> "lift_tm_lifted_apps: arg: " ^ Tac.term_to_string (quote ma) ^ " : " ^ Tac.term_to_string arg);
    let (ma, arg) = mode_cast m1 (ma, arg) in
    lift_tm_lifted_apps e (Tac.pack (Tac.Tv_App hd (arg, aq))) args m2 ctx0 strm_apps


  | _, (arg,_) :: _ ->
    fail "too many arguments for mode"
      (Ref.range_of_term hd)
      ["go_apps";
      "arg: " ^ Tac.term_to_string arg;
      "head: " ^ Tac.term_to_string hd;
      "mode: " ^ Tac.term_to_string (quote_mode m)]
  | _, [] ->
    let (tys, _) = get_exp_context hd e in
    let tm = lift_tm_lifted_apps_strm e hd ctx0 (List.rev strm_apps) tys tys in
    (m, tm)

and lift_tm_lifted_apps_strm (e: env) (hd: Tac.term) (ctx0: Tac.term) (strm_apps: list Tac.term) (tys: list Tac.typ) (tys_all: list Tac.typ): Tac.Tac Tac.term =
  match strm_apps, tys with
  | [], [] ->
    exp_weaken (PTB.mk_list tys_all) ctx0 hd
  | s :: strm_apps, t :: tys ->
    let tm = lift_tm_lifted_apps_strm e hd ctx0 strm_apps tys tys_all in
    let tm = exp_XLet t s tm in
    tm

  | _, _ ->
    fail "inconsistent number of applications for type"
      (Ref.range_of_term hd)
      ["lift_tm_lifted_apps_strm"]

// [@@plugin]
// TODO change arguments to (list (string & string)), support letrecs
let lift_tac (nm_src nm_core: string) : Tac.Tac (list Tac.sigelt) =
  let tac_env = Tac.top_env () in
  let m = Tac.cur_module () in
  let nm_src_m = Ref.implode_qn List.(m @ [nm_src]) in
  let nm_core_m = Ref.implode_qn List.(m @ [nm_core]) in
  let nm_src_m_exp = Ref.explode_qn nm_src_m in
  let lb_src = PTB.lookup_lb_top tac_env nm_src_m_exp in
  let se_src = match Ref.lookup_typ tac_env nm_src_m_exp with
    | None -> Tac.fail "impossible"
    | Some s -> s in
  let lb_mode = match mode_of_attrs (Ref.sigelt_attrs se_src) with
    | None -> Tac.fail "expected source function to have source_mode annotation"
    | Some m -> m in
  let e = env_nil [nm_src_m, lb_mode] in
  let nm_src_const = Tac.pack (Tac.Tv_Const (Ref.C_String nm_src_m)) in
  let tm = lb_src.lb_def in
  let _, tm = lift_tm e tm (Some lb_mode) in
  let _, se = core_sigelt e [`core_lifted] (Some nm_src_m) (Some nm_core_m) lb_mode tm in
  let extra_sigelts = List.rev (Tac.read e.extra_sigelts) in
  List.(extra_sigelts @ [se])

let lift_tac1 (nm_src: string) : Tac.Tac (list Tac.sigelt) =
  lift_tac nm_src (env_core_nm nm_src)