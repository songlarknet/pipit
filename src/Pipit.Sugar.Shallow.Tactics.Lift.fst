(* Lifting transform / syntactic sugar for streaming programs.

  This file defines a preprocessor tactic that tries to "lift" non-streaming
  operations to a streaming context. It's conceptually similar to inferring
  monadic binds, except that our streams are applicative and not monadic.

  For example, we could imagine writing a program:

  > let increment_every_element (element: stream int): stream int =
  >   element + 1

  This program isn't well-typed as it mixes integer operations with streams.
  We can insert applicative <$>, <*> and returns to make it well-typed:

  > let increment_every_element (element: stream int): stream int =
  >   (+) <$> element <*> return 1

  Manually inserting these primitives isn't too bad for small programs, but
  it gets noisy in large programs. Pipit has two additional complexities that
  make it even noisier.

  First, streams are restricted to store "statically-bounded" types, which in
  our case outlaws streams of functions. Unfortunately, the intermediate stream
  `(+) <$> element` has type `stream (int -> int)`,
  which we do not support as a runtime type. To work around this, we use a
  separate type for intermediate applications; this application type is
  restricted and can't be delayed or stored in stream variables.

  The second complexity is that we want to annotate each primitive with some
  unique identifier, so that a later common-subexpression-elimination pass can
  check whether two operations are equal.

  High-level question:
    * is this a massive hack? Should this use the new DSL framework instead?

  Implementation questions / limitations:
    * record constructors and record field accessors do not typecheck with FStar.Tactics.tc
    * mutual recursion isn't exposed by Tac.inspect. Exposing this would be a big change, wouldn't it?
*)
module Pipit.Sugar.Shallow.Tactics.Lift

module Table = Pipit.Prim.Table
module ShallowPrim = Pipit.Prim.Shallow
module Shallow = Pipit.Sugar.Shallow.Base
module SugarBase = Pipit.Sugar.Base
module PTB = Pipit.Tactics.Base
module PTC = Pipit.Tactics.Cse

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2
module TermEq = FStar.Reflection.V2.TermEq

module Range = FStar.Range

module List = FStar.List.Tot


(*** Attributes ***)
(* Mark as source program; to be lifted by autolifter (unused for now) *)
irreducible
let source = ()

(* For generated bindings *)
irreducible
let lifted = ()

(* For generated lifted primitives *)
irreducible
let lifted_prim = ()

(* For generated bindings; pointer back to original *)
irreducible
let of_source (nm: string) = ()

(*** Streaming interface stubs ***)
type stream (a: eqtype) {| Shallow.has_stream a |} = a

(* Recursive streams *)
assume val rec' (#a: eqtype) {| Shallow.has_stream a |} (f: stream a -> stream a): stream a
(* Delayed streams *)
assume val fby (#a: eqtype) {| Shallow.has_stream a |} (init: a) (strm: stream a): stream a
(* Uninitialised delay. This is "unsafe" in that the first value is undefined. *)
assume val pre (#a: eqtype) {| Shallow.has_stream a |} (strm: stream a): stream a
(* Non-delayed "x then y" *)
assume val (->^) (#a: eqtype) {| Shallow.has_stream a |} (x y: stream a): stream a
(* Check property: a property is a stream of booleans *)
assume val check (strm: stream bool): stream unit
(* Lift constant to stream *)
assume val lift (#a: eqtype) {| Shallow.has_stream a |} (x: a): stream a
(* Instantiate lemma with a pattern *)
assume val lemma_pattern: stream unit -> stream unit

(* Do not lift *)
let static (#a: Type) (x: a): a = x


(*** Implementations of stubs ***)
[@@lifted; of_source(`%rec')]
// private
let rec_impl (#a: eqtype) {| Shallow.has_stream a |} (f: Shallow.stream a -> Shallow.stream a): Shallow.stream a = Shallow.rec' f

[@@lifted; of_source(`%fby)]
// private
let fby_impl (#a: eqtype) {| Shallow.has_stream a |} (init: a) (strm: Shallow.stream a): Shallow.stream a = Shallow.fby init strm

[@@lifted; of_source(`%pre)]
// private
let pre_impl (#a: eqtype) {| Shallow.has_stream a |} (strm: Shallow.stream a): Shallow.stream a = Shallow.pre strm

[@@lifted; of_source(`%op_Subtraction_Greater_Hat)]
// private
let arrow_impl (#a: eqtype) {| Shallow.has_stream a |} (x y: Shallow.stream a): Shallow.stream a = Shallow.(x ->^ y)


(* Check property: a property is a stream of booleans *)
[@@lifted; of_source(`%check)]
// private
let check_impl (eprop: Shallow.stream bool): Shallow.stream unit = Shallow.check "" eprop

(* Lift constant to stream *)
[@@lifted; of_source(`%lift)]
// private
let lift_impl (#a: eqtype) {| Shallow.has_stream a |} (x: a): Shallow.stream a = Shallow.const x

// private
[@@"opaque_to_smt"]
let liftP'prim
  (#ft: Table.funty ShallowPrim.shallow_type)
  (f: SugarBase.prim ShallowPrim.table ft):
      SugarBase._s_apps ShallowPrim.table ft =
  SugarBase.liftP'prim f

// private
[@@"opaque_to_smt"]
let liftP'apply
  (#a: eqtype)
  {| Shallow.has_stream a |}
  (#ft: Table.funty ShallowPrim.shallow_type)
  (f: SugarBase._s_apps ShallowPrim.table (Table.FTFun (Shallow.shallow a) ft))
  (ea: Shallow.stream a):
      SugarBase._s_apps ShallowPrim.table ft =
  SugarBase.liftP'apply f ea

// private
[@@"opaque_to_smt"]
let liftP'stream
  (#a: eqtype)
  {| Shallow.has_stream a |}
  (ea: SugarBase._s_apps ShallowPrim.table (Table.FTVal (Shallow.shallow a))):
      Shallow.stream a =
  SugarBase.liftP'stream ea

let fail (#a: Type) (msg: string) (rng: Range.range) (ctx: list string): Tac.Tac a =
  let str0 = "Lift transform: failure at " ^ Tac.range_to_string rng ^ "\n  " ^ msg in
  let str = List.fold_left (fun str str' -> str ^ "\n    * " ^ str') str0 ctx in
  Tac.fail str


(*
  Simple preprocessor to enable more streamy syntax.
  For the most part, this leaves the term as-is. Recursive let bindings
  are translated to stream recursion, if there are no arguments.
  Usage:

  > [@@FStar.Tactics.preprocess_with preprocess; source]
  > let stream_of (cond: stream bool): stream int =
  >   let rec x = 0 `fby` x + (if cond then 1 else 0) in
  >   x

  which gets desugared to:

  > let stream_of (cond: stream bool): stream int =
  >   let x = Pipit.Sugar.Stubs.rec' (fun x -> 0 `fby` x + (if cond then 1 else 0)) in
  >   x

  We also insert unknown type ascriptions for compound expressions that can be
  annoying to re-typecheck. Specifically, we add type ascriptions to pattern match
  scrutinees and branches.

 *)
let rec preprocess_go (t: Tac.term): Tac.Tac (option Tac.term) =
  let progress (t: Tac.term) =
    match preprocess_go t with
    | None -> (t, false)
    | Some t -> (t, true)
  in
  match Tac.inspect t with
  | Tac.Tv_Var _ | Tac.Tv_BVar _ | Tac.Tv_FVar _
  | Tac.Tv_Const _ ->
    None

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let (hd, hdp) = progress hd in
    let (arg, argp) = progress arg in
    if hdp || argp
    then Some (Tac.pack (Tac.Tv_App hd (arg, aqual)))
    else None

  | Tac.Tv_Abs bv tm ->
    (match preprocess_go tm with
    | Some tm -> Some (Tac.pack (Tac.Tv_Abs bv tm))
    | None -> None)

  | Tac.Tv_Let true attrs b def body ->
    // Letrec: recursive streams do not have lambdas; recursive functions do
    (match Tac.inspect def with
    | Tac.Tv_Abs _ _ ->
      let (def, defp) = progress def in
      let (body, bodyp) = progress body in

      if defp || bodyp
      then Some (Tac.pack (Tac.Tv_Let true attrs b def body))
      else None
    | ti ->
      // type annotations on letrecs are parsed as ascriptions, so pull them out
      let (body,ty) = match ti with
        | Tac.Tv_AscribedT body ty None _
        | Tac.Tv_AscribedC body (Tac.C_Total ty) None _
        -> (body, ty)
        | _ -> (body, b.sort)
      in
      let b = { b with sort = ty } in
      let (def, _) = progress def in
      let (body, _) = progress body in
      let defabs = Tac.pack (Tac.Tv_Abs b def) in
      Some (Tac.pack (Tac.Tv_Let false attrs b (`rec' (`#defabs)) body)))

  | Tac.Tv_Let false attrs b def body ->
    let (def, defp) = progress def in
    let (body, bodyp) = progress body in
    if defp || bodyp
    then Some (Tac.pack (Tac.Tv_Let false attrs b def body))
    else None

  | Tac.Tv_Match scrut ret brs ->
    let progress_ascribe tm =
      let (tm, p) = progress tm in
      match Tac.inspect tm with
      | Tac.Tv_AscribedT _ _ _ _
      | Tac.Tv_AscribedC _ _ _ _ -> (tm, p)
      | _ -> (Tac.pack (Tac.Tv_AscribedT tm (`_) None false), true)
    in

    let (scrut,p) = progress_ascribe scrut in
    let pref = Tac.alloc p in
    let brs = Tac.map (fun (pat,br) ->
      let (br, p') = progress_ascribe br in
      if p' then Tac.write pref true;
      (pat, br)) brs in
    if Tac.read pref
    then Some (Tac.pack (Tac.Tv_Match scrut ret brs))
    else None

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    (match preprocess_go tm with
    | Some tm -> Some (Tac.pack (Tac.Tv_AscribedT tm ty tac use_eq))
    | None -> None)

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    (match preprocess_go tm with
    | Some tm -> Some (Tac.pack (Tac.Tv_AscribedC tm cmp tac use_eq))
    | None -> None)

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ | Tac.Tv_UInst _ _
  | Tac.Tv_Arrow  _ _ | Tac.Tv_Type   _
  | Tac.Tv_Refine _ _ | Tac.Tv_Unknown     -> None

  | Tac.Tv_Unsupp -> fail ("cannot unpack unsupported term: " ^ Tac.term_to_string t) (Tac.range_of_term t) ["in preprocess tactic"]

let preprocess (t: Tac.term): Tac.Tac Tac.term =
  match preprocess_go t with
  | None -> t
  | Some t -> t



(*** Autolifter ***)

(*** Internal stream combinators and inserted calls ***)

type mode = | Stream | Static | ModeFun: mode -> explicit: bool -> mode -> mode

let debug_print (str: unit -> Tac.Tac string): Tac.Tac unit =
  if Tac.ext_getv "pipit:lift:debug" <> ""
  then (
    let ms = Tac.curms () in
    Tac.print (Tac.term_to_string (quote ms) ^ ": " ^ str ())
  )

let core_sigelt (attrs: list Tac.term) (nm_src nm_core: option string) (tm: Tac.term): Tac.Tac (Tac.name & Tac.sigelt) =
  let nm_def = match nm_core with
    | Some n -> Ref.explode_qn n
    | None ->
      let u = Tac.fresh () in
      List.(Tac.cur_module () @ ["_core_def_" ^ string_of_int u])
  in

  let ty = Tac.pack Tac.Tv_Unknown in
  // TODO: support recursive bindings
  let lb_core: Tac.letbinding = {
    lb_fv  = Tac.pack_fv nm_def;
    lb_us  = [];
    lb_typ = ty;
    lb_def = tm;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let {isrec=false; lbs=[lb_core]} in
  let se: Tac.sigelt = Tac.pack_sigelt sv in
  let attrs = match nm_src with
    | Some nm -> (`of_source (`#(Tac.pack (Tac.Tv_Const (Ref.C_String nm))))) :: attrs
    | None -> attrs in
  debug_print (fun () -> "core_sigelt: " ^ Ref.implode_qn nm_def);
  debug_print (fun () -> "core_sigelt: " ^ Tac.term_to_string tm);
  nm_def, Ref.set_sigelt_attrs attrs se

noeq
type env = {
  tac_env: Tac.env;
  mode_env: list (nat & mode);
  lifted_env: list (Ref.name & Ref.name);
  extra_sigelts: Tac.tref (list Tac.sigelt);
  prim_env: Tac.tref (list (Ref.name & Ref.name));
}

let env_lifted_mapping (tac_env: Tac.env) (lift_fv: Ref.fv): Tac.Tac (option (Ref.name & Ref.name)) =
  let lift_nm = Tac.inspect_fv lift_fv in
  let lift_se = Tac.lookup_typ tac_env lift_nm in
  let rec go (attrs: list Tac.term): Tac.Tac (option (Ref.name & Ref.name)) =
    match attrs with
    | [] -> None
    | hd :: tl ->
      let (hd,args) = Tac.collect_app hd in
      if TermEq.term_eq hd (`of_source)
      then (match args with
        | [(arg,_)] ->
          (match Tac.inspect arg with
          | Tac.Tv_Const (Ref.C_String nm) -> Some (lift_nm, Tac.explode_qn nm)
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

let env_top (tac_env: Tac.env): Tac.Tac env =
  let mode_env = [] in
  let lifts = Ref.lookup_attr (`lifted) tac_env in
  let prims = Ref.lookup_attr (`lifted_prim) tac_env in
  let lifted_env = Tac.filter_map (env_lifted_mapping tac_env) lifts in
  let prim_env = Tac.filter_map (env_lifted_mapping tac_env) prims in
  let prim_env = Tac.alloc prim_env in
  let extra_sigelts = Tac.alloc [] in
  { tac_env; mode_env; lifted_env; prim_env; extra_sigelts; }

let env_nil (): Tac.Tac env = env_top (Tac.top_env ())

let env_push (b: Tac.binder) (m: mode) (e: env): env =
  { e with
    tac_env  = Ref.push_namedv e.tac_env (Ref.pack_namedv b);
    mode_env = (b.uniq, m) :: e.mode_env;
  }

(* Get mode (stream / non-stream) of local binding. We also get the de bruijn
  index of the stream bindings, though this is currently unused. *)
let env_get_mode (b: Tac.namedv) (e: env) (rng: Range.range): Tac.Tac (mode & nat) =
  let rec go (bs: list (nat & mode)) (strm_ix: nat): Tac.Tac (mode & nat) =
    match bs with
    | [] ->
      fail ("no such binder: b" ^ Tac.namedv_to_string b)
        rng
        ["(internal error)"]
    | (uniq, m) :: bs ->
      if uniq = b.uniq
      then (m, strm_ix)
      else if m = Stream
      then go bs (strm_ix + 1)
      else go bs strm_ix
  in go e.mode_env 0

let rec env_push_pat (p: Tac.pattern) (m: mode) (e: env): Tac.Tac env =
  match p with
  | Tac.Pat_Constant _ -> e
  | Tac.Pat_Cons c ->
    Tac.fold_left (fun e (p,_) -> env_push_pat p m e) e c.subpats
  | Tac.Pat_Var v ->
    env_push (Tac.namedv_to_binder v.v (Tac.unseal v.sort)) m e
  | Tac.Pat_Dot_Term _ -> e

let env_lifted_lookup (fv: Ref.fv) (lifts: list (Tac.name & Tac.name)): Tac.Tac (option Ref.fv) =
  let nm = Tac.inspect_fv fv in
  let rec go (bs: list (Ref.name & Ref.name)): Tac.Tac (option Ref.fv) =
    match bs with
    | [] -> None
    | (lifted,src) :: tl ->
      if nm = src
      then Some (Tac.pack_fv lifted)
      else go tl
  in go lifts

let env_get_lifted_of_source (fv: Ref.fv) (e: env): Tac.Tac Ref.fv =
  match env_lifted_lookup fv e.lifted_env with
  | None -> fv
  | Some x -> x

let env_get_lifted_prim_of_source (fv: Ref.fv) (e: env): Tac.Tac (option Ref.fv) =
  env_lifted_lookup fv (Tac.read e.prim_env)


let stream_nm_explode: list string = Ref.explode_qn (`%stream)
let shallow_stream_nm_explode: list string = Ref.explode_qn (`%Shallow.stream)

let element_of_stream_ty (ty: Tac.term): Tac.Tac (option Tac.term) =
  // TODO: unify / match?
  let (hd, args) = Tac.collect_app ty in
  match Tac.inspect_unascribe hd, args with
  | Tac.Tv_FVar fv, [(elty, _); _] ->
    let fv' = Tac.inspect_fv fv in
    if fv' = stream_nm_explode || fv' = shallow_stream_nm_explode
    then Some elty
    else None
  | _ -> None

let element_of_stream_ty_force (ty: Tac.term): Tac.Tac Tac.term =
  match element_of_stream_ty ty with
  | None -> ty
  | Some t -> t

let rec mode_of_ty (ty: Tac.term): Tac.Tac mode =
  match element_of_stream_ty ty, Tac.inspect_unascribe ty with
  | Some _, _ -> Stream
  | None, Tac.Tv_Arrow arg (Tac.C_Total res)
  | None, Tac.Tv_Arrow arg (Tac.C_GTotal res)
  // We don't support general effects, but parse them anyway in case the effect is Tot
  | None, Tac.Tv_Arrow arg (Tac.C_Eff _ _ res _ _) ->
    ModeFun (mode_of_ty arg.sort) (PTB.qual_is_explicit arg.qual) (mode_of_ty res)
  | None, Tac.Tv_Arrow arg (Tac.C_Lemma _ _ _) ->
    ModeFun (mode_of_ty arg.sort) (PTB.qual_is_explicit arg.qual) Static
  | t ->
    Static

let mode_join (rng: Range.range) (m1 m2: mode): Tac.Tac mode = match m1, m2 with
  | Stream, Static -> Stream
  | Static, Stream -> Stream
  | Static, Static -> Static
  | _, _ -> if m1 = m2 then m1 else fail ("cannot join incompatible modes: " ^ Tac.term_to_string (quote (m1, m2))) rng []

let mode_cast (m_expect: mode) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  (match mt, m_expect with
  | (Static, tm), Stream -> (Stream, (`SugarBase.const (`#tm)))
  | (m, tm), _ -> (m, tm))

let rec lift_mode (m: mode): mode =
  match m with
  | Static -> Stream
  | Stream -> Stream
  // XXX cannot lift functions
  | ModeFun m1 e m2 -> ModeFun Stream e (lift_mode m2)

let type_cast (ty: Tac.term) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  match Tac.inspect ty with
  | Tac.Tv_Unknown ->
    mt
  | _ ->
    (match mt, mode_of_ty ty with
    | (Static, tm), Stream -> (Stream, (`SugarBase.const (`#tm)))
    | _ -> mt)

let joins_modes (rng: Range.range) (mts: list (mode & Tac.term)): Tac.Tac (mode & list Tac.term) =
  match mts with
  | (m0, tm) :: mts' ->
    let ms' = List.map fst mts' in
    let m = Tac.fold_left (mode_join rng) m0 ms' in
    (m, Tac.map (fun x -> snd (mode_cast m x)) mts)
  | [] -> (Static, [])

(* Remove stream constructors from primitive before lifting (HACK?).

  The idea is that if we have a polymorphic primitive applied to streams:
  > fun (xs ys: stream int) ->
  >   let pairs = (xs, ys) in
  >   fst pairs

  Then that will get inferred types and implicits:
  > fun (xs ys: stream int) ->
  >   let pairs: (stream int & stream int) = (xs, ys) in
  >   fst #(stream int) #(stream int) pairs

  But we really want to generate

  > fun (xs ys: stream_core int) ->
  >   let pairs: stream_core (int & int) = (Mktuple2 #int #int) <$> xs <*> ys in
  >   (fst #(int) #(int)) <$> pairs

  This gets half of the way there -- unwrapping the streams in the primops.
*)
let unwrap_prim (prim: Tac.term): Tac.Tac Tac.term =
  let go (t: Tac.term): Tac.Tac Tac.term =

    match element_of_stream_ty t with
    | Some t' -> t'
    | None -> t
  in
  Tac.visit_tm go prim

let lift_prim_gen (e: env) (prim: Tac.term): Tac.Tac Tac.term =
  let prim = unwrap_prim prim in
  let ty = PTB.tc_unascribe e.tac_env prim in
  let nm =
    match Tac.inspect_unascribe prim with
    | Tac.Tv_FVar fv ->
      let fv' = Tac.inspect_fv fv in
      Some fv'
    | _ -> None
  in
  let nm_tm =
    match nm with
    | Some f -> (quote (Some f))
    | None -> (`None)
  in
  let (args,res) = Tac.collect_arr ty in
  let res = PTB.returns_of_comp res in
  let ft =
    List.fold_right (fun a b -> (`Table.FTFun (Shallow.shallow (`#a)) (`#b))) args (`Table.FTVal (Shallow.shallow (`#res)))
  in
  let argnamedvs = Tac.map
    (fun ty ->
      let tys = `Shallow.stream (`#ty) in
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
  let prim = (`liftP'prim (ShallowPrim.mkPrim (`#nm_tm) (`#ft) (`#prim))) in
  // TODO: deal with implicit args
  let lift = List.fold_left
    (fun hd (ty,nv) ->
      let tm = Tac.pack (Tac.Tv_Var nv) in
      `liftP'apply #(`#ty) (`#hd) (`#tm))
    prim argnamedvs
  in
  let lift = `liftP'stream #(`#res) (`#lift) in
  let abs = List.fold_right
    (fun (ty,nv) hd ->
      let tys = `Shallow.stream (`#ty) in
      Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder nv tys) hd))
    argnamedvs lift
  in
  abs

let lift_prim (e: env) (prim: Tac.term): Tac.Tac Tac.term =
  match Tac.inspect prim with
  | Tac.Tv_FVar fv ->
    (match env_get_lifted_prim_of_source fv e with
    | Some fv' ->
      Tac.pack (Tac.Tv_FVar fv')
    | None ->
      let nm = Tac.inspect_fv fv in
      let prim = lift_prim_gen e prim in
      let nm_def, sigelt = core_sigelt [`lifted_prim] (Some (Tac.implode_qn nm)) None prim in
      Tac.write e.prim_env ((nm_def, nm) :: Tac.read e.prim_env);
      Tac.write e.extra_sigelts (sigelt :: Tac.read e.extra_sigelts);
      (Tac.pack (Tac.Tv_FVar (Tac.pack_fv nm_def))))
  | _ -> lift_prim_gen e prim

let lift_stream_match (e: env) (tscrut: Tac.term) (tret: Tac.term) (scrut: Tac.term) (ret: option Tac.match_returns_ascription) (brs: list (Tac.pattern & Tac.term)): Tac.Tac Tac.term =
  let mk_namedv (pp: string) (ty: Tac.term) =
    { uniq = Tac.fresh (); sort = Tac.seal ty; ppname = Ref.as_ppname pp } <: Tac.namedv
  in
  let nscrut = mk_namedv "scrut" tscrut in
  let nbrs = Tac.map (fun (pat,tm) ->
    (mk_namedv "branch" tret, pat, tm)) brs in
  let brs = List.map (fun (nm,pat,tm) -> (pat, Tac.pack (Tac.Tv_Var nm))) nbrs in
  let xmatch = Tac.pack (Tac.Tv_Match (Tac.pack (Tac.Tv_Var nscrut)) ret brs) in
  let rec go_abs hd nms: Tac.Tac Tac.term = match nms with
    | [] -> hd
    | (nm,ty)::nms ->
      go_abs (Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder nm ty) hd)) nms
  in
  let rec go_app hd tms: Tac.Tac Tac.term = match tms with
    | [] -> hd
    | (tm,ty)::tms ->
      go_app (Tac.pack (Tac.Tv_App hd (tm, Ref.Q_Explicit))) tms
  in
  let abs = go_abs xmatch (List.rev ((nscrut, tscrut) :: List.map (fun (nm,_,_) -> (nm, tret)) nbrs)) in
  let abs = lift_prim e abs in
  let app = go_app abs ((scrut, tscrut) :: List.map (fun (_,_,tm) -> (tm, tret)) nbrs) in
  app

let lift_ty_visit (t: Tac.term): Tac.Tac Tac.term =
  match Tac.inspect t with
  | Tac.Tv_FVar fv ->
    let fv' = Tac.inspect_fv fv in
    if fv' = stream_nm_explode
    then (`Shallow.stream)
    else t
  // | Tac.Tv_AscribedC e c topt use_eq ->
  //   // F* bug: visit_tm does not descend into computations
  //   let c = Tac.visit_comp go (Ref.pack_comp c) in
  //   Tac.pack (Tac.Tv_AscribedC e (Ref.inspect_comp c) topt use_eq)
  | _ -> t

let lift_ty: Tac.term -> Tac.Tac Tac.term =
  Tac.visit_tm lift_ty_visit

let lift_ty_binder (b: Tac.binder): Tac.Tac Tac.binder =
  let sort = lift_ty b.sort in
  { b with sort = sort }

let lift_ty_simple_binder (b: Tac.simple_binder): Tac.Tac Tac.simple_binder =
  let sort = lift_ty b.sort in
  { b with sort = sort }

let rec lift_tm (e: env) (t: Tac.term): Tac.Tac (mode & Tac.term) =
  let go_stream (e: env) (t: Tac.term) =
    let (m, t) = lift_tm e t in
    match m with
    | Static -> (`SugarBase.const (`#t))
    | Stream -> t
    | ModeFun _ _ _ ->
      fail ("cannot lift function to stream: " ^ Tac.term_to_string t)
        (Ref.range_of_term t)
        []
  in
  let ti = Tac.inspect t in
  match Tac.inspect t with
  | Tac.Tv_Var (v: Tac.namedv) ->
    (fst (env_get_mode v e (Ref.range_of_term t)), t)
  | Tac.Tv_BVar (v: Tac.bv) ->
    fail
      ("unexpected bvar; expected named variables only " ^ Tac.term_to_string t)
      (Ref.range_of_term t) []
  | Tac.Tv_FVar _ | Tac.Tv_UInst _ _ ->
    let ty = PTB.tc_unascribe e.tac_env t in
    let m  = mode_of_ty ty in
    debug_print (fun _ -> "fvar: " ^ Tac.term_to_string t ^ " mode: " ^ Tac.term_to_string (quote m) ^ " ty: " ^  Tac.term_to_string ty);
    (m, lift_ty_visit t)
  | Tac.Tv_Const (vc: Tac.vconst) ->
    (Static, t)

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let rec go_apps m hd args: Tac.Tac (mode & Tac.term) = match m, args with
      | ModeFun _ false m2, (_,Ref.Q_Explicit)::_ ->
        go_apps m2 hd args

      | ModeFun m1 mq m2, (arg,aq)::args ->
        let (ma, arg) = lift_tm e arg in
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
          let prim = lift_prim e hd in
          let m2 = lift_mode m2 in
          go_apps m2 (Tac.pack (Tac.Tv_App prim (arg, aq))) args
        | _, _ ->
          let (ma, arg) = mode_cast m1 (ma, arg) in
          go_apps m2 (Tac.pack (Tac.Tv_App hd (arg, aq))) args)

      | _, (arg,_) :: _ ->
        fail "too many arguments for mode"
          (Ref.range_of_term arg)
          ["go_apps";
          "arg: " ^ Tac.term_to_string arg;
          "head: " ^ Tac.term_to_string hd;
          "mode: " ^ Tac.term_to_string (quote m)]
      | _, [] -> (m, hd)
    in
    let (hd, args) = Tac.collect_app t in
    let (mh, hd) = lift_tm e hd in
    let hd = match Tac.inspect hd with
      | Tac.Tv_FVar fv ->
        Tac.pack (Tac.Tv_FVar (env_get_lifted_of_source fv e))
      | _ -> hd
    in
    debug_print (fun () -> "app hd: " ^ Tac.term_to_string hd ^ " mode: " ^ Tac.term_to_string (quote mh) ^ " ty: " ^  Tac.term_to_string (PTB.tc_unascribe e.tac_env hd));
    // (static x) stops lifting of x, but if the result is applied to
    // another argument, we still want to lift that:
    // > lift ((static x) y) ==> x (lift y)
    if TermEq.term_eq hd (`static)
    then match args with
         | (hd, Ref.Q_Explicit)::args -> go_apps (mode_of_ty (PTB.tc_unascribe e.tac_env hd)) (lift_ty hd) args
         | (ty, Ref.Q_Implicit)::(hd, Ref.Q_Explicit)::args -> go_apps (mode_of_ty ty) (lift_ty hd) args
         | _ -> fail "static: impossible: expected application" (Ref.range_of_term t) []
    else go_apps mh hd args

  | Tac.Tv_Abs bv tm ->
    debug_print (fun () -> "Abs: lift_tm with " ^ Tac.term_to_string bv.sort);
    let m1 = mode_of_ty bv.sort in
    let (m2, tm) = lift_tm (env_push bv m1 e) tm in
    let bv = lift_ty_binder bv in
    (ModeFun m1 (PTB.qual_is_explicit bv.qual) m2, Tac.pack (Tac.Tv_Abs bv tm))

  | Tac.Tv_Let true attrs b def body ->
    debug_print (fun () -> "letrec: binder type: " ^ Tac.term_to_string (b.sort));
    let mdef = mode_of_ty b.sort in
    let e = env_push b mdef e in
    let (_mdef, def) = lift_tm e def in
    let (mb, body) = lift_tm e body in
    let b = lift_ty_simple_binder b in
    (mb, Tac.pack (Tac.Tv_Let true attrs b def body))
  | Tac.Tv_Let false attrs b def body ->
    let (md, def) = lift_tm e def in
    let (md, def) = type_cast b.sort (md,def) in
    let (mb, body) = lift_tm (env_push b md e) body in
    let lett = match md, mb with
      | Stream, Stream ->
        // ensure type is of form `stream elt`
        let elty = element_of_stream_ty_force b.sort in
        let b = { b with sort = (`Shallow.stream (`#elty)) } <: Tac.simple_binder
        in
        let b = lift_ty_simple_binder b in
        let bodyabs = Tac.pack (Tac.Tv_Abs b body) in
        Shallow.(`(let^) (`#def) (`#bodyabs))
      | _, _ ->
        let b = lift_ty_simple_binder b in
        Tac.pack (Tac.Tv_Let false attrs b def body)
    in
    (mb, lett)

  | Tac.Tv_Match scrut0 ret brs0 ->
    // TODO: lift_tm on ret
    let (ms, scrut) = lift_tm e scrut0 in
    (match ms with
    | Static ->
      debug_print (fun () -> "match: static scrutinee " ^ Tac.term_to_string scrut);
      let mts = Tac.map (fun (pat,tm) -> lift_tm (env_push_pat pat Static e) tm) brs0 in
      let (mbrs, ts) = joins_modes (Ref.range_of_term t) mts in
      let brs = Pipit.List.zip2 (List.map fst brs0) ts in
      (mbrs, Tac.pack (Tac.Tv_Match scrut ret brs))
    | Stream ->
      debug_print (fun () -> "match: stream scrutinee " ^ Tac.term_to_string scrut);
      // XXX: the current semantics for streaming-matches is more of a "select"
      // than a match: all of the branches are eagerly evaluated, and then we
      // just choose which to return based on the scrutinee
      let rec check_pat p: Tac.Tac unit = match p with
        | Tac.Pat_Constant _ -> ()
        | Tac.Pat_Cons c -> Tac.iter (fun (p,_) -> check_pat p) c.subpats
        | Tac.Pat_Var _ ->
          fail ("streaming patterns can't bind variables (TODO)")
            (Ref.range_of_term t) ["in pattern-match"]
        // not sure what this means...
        | Tac.Pat_Dot_Term _ -> ()
      in
      let check_pat_top p: Tac.Tac unit = match p with
        // TODO: assert Pat_Var binder is `_` / not mentioned
        | Tac.Pat_Var _ -> ()
        | p -> check_pat p
      in
      let brs = Tac.map (fun (pat,tm) -> check_pat_top pat; (pat, go_stream e tm)) brs0 in

      // XXX: WRONG COMPLEXITY: this typechecking must be very bad for nested pattern matches
      let tscrut = element_of_stream_ty_force (PTB.tc_unascribe e.tac_env scrut0) in
      let tret = match brs0 with
       | (_, tm) :: _ ->
        element_of_stream_ty_force (PTB.tc_unascribe e.tac_env tm)
       | [] -> Tac.pack Tac.Tv_Unknown in
      (Stream, lift_stream_match e tscrut tret scrut ret brs)
    | ModeFun _ _ _ ->
      fail "match scrutinee cannot be function"
        (Ref.range_of_term scrut) ["in pattern match"])

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    debug_print (fun () -> "AscribedT: " ^ Tac.term_to_string ty);
    let (mm, tm) = lift_tm e tm in
    let (mm, tm) = type_cast ty (mm, tm) in
    let ty = match mm, element_of_stream_ty ty with
      | Stream, None -> (`Shallow.stream (`#ty))
      | _ -> ty
    in
    (mm, Tac.pack (Tac.Tv_AscribedT tm (lift_ty ty) tac use_eq))

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    (match cmp with
    | Tac.C_Total ty ->
      debug_print (fun () -> "AscribedC: " ^ Tac.term_to_string ty);
      let (mm, tm) = lift_tm e tm in
      let (mm, tm) = type_cast ty (mm, tm) in
      let ty = match mm, element_of_stream_ty ty with
        | Stream, None -> (`Shallow.stream (`#ty))
        | _ -> ty
      in
      (mm, Tac.pack (Tac.Tv_AscribedC tm (Tac.C_Total (lift_ty ty)) tac use_eq))
      // TODO lemmas etc?
    | _ ->
      fail ("unsupported: type ascriptions on effects: " ^ Tac.comp_to_string cmp)
        (Ref.range_of_term t) [])

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ | Tac.Tv_Arrow  _ _ | Tac.Tv_Type   _
  | Tac.Tv_Refine _ _ | Tac.Tv_Unknown     -> (Static, lift_ty t)

  | Tac.Tv_Unsupp ->
    fail ("lift failed: cannot inspect term: " ^ Tac.term_to_string t)
      (Ref.range_of_term t) ["(unsupported term)"]


let autolift_bind1 (e: env) (nm nm_core: string): Tac.Tac Tac.sigelt =
  let lb_src = PTB.lookup_lb_top e.tac_env (Ref.explode_qn nm) in

  let _, tm = lift_tm e lb_src.lb_def in

  let _, se = core_sigelt [`lifted] (Some nm) (Some nm_core) tm in
  se

// TODO: it would be nice to make this a plugin, but the local letrecs mess up the extraction
// [@@plugin]
let autolift_binds (nms: list string): Tac.Tac (list Tac.sigelt) =
  let e = env_nil () in
  let elts = Tac.map (fun nm -> autolift_bind1 e nm (nm ^ "_core")) nms in
  List.(Tac.read e.extra_sigelts @ elts)
