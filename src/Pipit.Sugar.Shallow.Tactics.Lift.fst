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

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2
module TermEq = FStar.Reflection.V2.TermEq

module Range = FStar.Range

module List = FStar.List.Tot


(*** Attributes ***)
(* Mark as source program; to be lifted by autolifter *)
irreducible
let source = ()

(* For generated bindings *)
irreducible
let core = ()

(* For generated bindings; pointer back to original *)
irreducible
let of_source (nm: string) = ()

(*** Streaming interface stubs ***)
type stream (a: eqtype) {| Shallow.has_stream a |} = a

(* Recursive streams *)
assume val rec' (#a: eqtype) {| Shallow.has_stream a |} (f: stream a -> stream a): stream a
(* Delayed streams *)
assume val fby (#a: eqtype) {| Shallow.has_stream a |} (init: a) (strm: stream a): stream a
(* Check property: a property is a stream of booleans *)
assume val check (strm: stream bool): stream unit
(* Lift constant to stream *)
assume val lift (#a: eqtype) {| Shallow.has_stream a |} (x: a): stream a
(* Do not lift *)
let static (#a: Type) (x: a): a = x

(*** Implementations of stubs ***)
[@@core; of_source(`%rec')]
// private
let rec_impl (#a: eqtype) {| Shallow.has_stream a |} (f: Shallow.stream a -> Shallow.stream a): Shallow.stream a = Shallow.rec' f

[@@core; of_source(`%fby)]
// private
let fby_impl (#a: eqtype) {| Shallow.has_stream a |} (init: a) (strm: Shallow.stream a): Shallow.stream a = Shallow.fby init strm
//TODO etc

// private
let liftP'prim
  (#ft: Table.funty ShallowPrim.shallow_type)
  (f: SugarBase.prim ShallowPrim.table ft):
      SugarBase._s_apps ShallowPrim.table ft =
  SugarBase.liftP'prim f

// private
let liftP'apply
  (#a: eqtype)
  {| Shallow.has_stream a |}
  (#ft: Table.funty ShallowPrim.shallow_type)
  (f: SugarBase._s_apps ShallowPrim.table (Table.FTFun (Shallow.shallow a) ft))
  (ea: Shallow.stream a):
      SugarBase._s_apps ShallowPrim.table ft =
  SugarBase.liftP'apply f ea

// private
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

 *)
let rec preprocess (t: Tac.term): Tac.Tac Tac.term =
  let go = preprocess in
  match Tac.inspect t with
  | Tac.Tv_Var _ | Tac.Tv_BVar _ | Tac.Tv_FVar _
  | Tac.Tv_Const _ ->
    t

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    // TODO: F* bug: preprocess cannot re-pack record applications, so maybe we should avoid re-packing here unless something changed. Type needs to change to (term -> option term).
    Tac.pack (Tac.Tv_App (go hd) (go arg, aqual))

  | Tac.Tv_Abs bv tm ->
    Tac.pack (Tac.Tv_Abs bv (go tm))

  | Tac.Tv_Let true attrs b def body ->
    // Letrec: recursive streams do not have lambdas; recursive functions do
    (match Tac.inspect def with
    | Tac.Tv_Abs _ _ ->
      let def = go def in
      let body = go body in
      Tac.pack (Tac.Tv_Let true attrs b def body)
    | _ ->
      let def = go def in
      let body = go body in
      let defabs = Tac.pack (Tac.Tv_Abs b def) in
      Tac.pack (Tac.Tv_Let false attrs b (`rec' (`#defabs)) body))

  | Tac.Tv_Let false attrs b def body ->
    let def = go def in
    let body = go body in
    Tac.pack (Tac.Tv_Let false attrs b def body)

  | Tac.Tv_Match scrut ret brs ->
    let scrut = go scrut in
    let brs = Tac.map (fun (pat,br) -> (pat, go br)) brs in
    Tac.pack (Tac.Tv_Match scrut ret brs)

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    Tac.pack (Tac.Tv_AscribedT (go tm) ty tac use_eq)

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    Tac.pack (Tac.Tv_AscribedC (go tm) cmp tac use_eq)

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ | Tac.Tv_UInst _ _
  | Tac.Tv_Arrow  _ _ | Tac.Tv_Type   _
  | Tac.Tv_Refine _ _ | Tac.Tv_Unknown     -> t

  | Tac.Tv_Unsupp -> fail ("cannot unpack unsupported term: " ^ Tac.term_to_string t) (Tac.range_of_term t) ["in preprocess tactic"]




(*** Autolifter ***)

(*** Internal stream combinators and inserted calls ***)

type mode = | Stream | Static | ModeFun: mode -> explicit: bool -> mode -> mode

let debug_print (str: unit -> Tac.Tac string): Tac.Tac unit =
  if Tac.ext_getv "pipit:lift:debug" <> ""
  then Tac.print (str ())

noeq
type env = {
  tac_env: Tac.env;
  mode_env: list (nat & mode);
  core_env: list (Ref.name & Ref.name);
}

let env_core_mapping (tac_env: Tac.env) (core_fv: Ref.fv): Tac.Tac (option (Ref.name & Ref.name)) =
  let core_nm = Tac.inspect_fv core_fv in
  let core_se = Tac.lookup_typ tac_env core_nm in
  let rec go (attrs: list Tac.term): Tac.Tac (option (Ref.name & Ref.name)) =
    match attrs with
    | [] -> None
    | hd :: tl ->
      let (hd,args) = Tac.collect_app hd in
      if TermEq.term_eq hd (`of_source)
      then (match args with
        | [(arg,_)] ->
          (match Tac.inspect arg with
          | Tac.Tv_Const (Ref.C_String nm) -> Some (core_nm, Tac.explode_qn nm)
          | _ -> fail
            ("cannot parse attribute " ^ Tac.term_to_string hd)
            (Tac.range_of_term arg)
            ["in binding " ^ Ref.implode_qn core_nm])
        | _ -> go tl)
      else go tl
  in
  match core_se with
  | Some se ->
    let attrs = Ref.sigelt_attrs se in
    go attrs
  | None -> None

let env_top (tac_env: Tac.env): Tac.Tac env =
  let mode_env = [] in
  let cores = Ref.lookup_attr (`core) tac_env in
  let core_env = Tac.filter_map (env_core_mapping tac_env) cores in
  { tac_env; mode_env; core_env; }

let env_nil (): Tac.Tac env = env_top (Tac.top_env ())

let env_push (b: Tac.binder) (m: mode) (e: env): env =
  { tac_env  = Ref.push_namedv e.tac_env (Ref.pack_namedv b);
    mode_env = (b.uniq, m) :: e.mode_env;
    core_env = e.core_env; }

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

let env_get_core_of_source (fv: Ref.fv) (e: env): Ref.fv =
  let nm = Tac.inspect_fv fv in
  let rec go (bs: list (Ref.name & Ref.name)): Ref.fv =
    match bs with
    | [] -> fv
    | (core,src) :: tl ->
      if nm = src
      then Tac.pack_fv core
      else go tl
  in go e.core_env

// XXX: can we kill this?
let assert_type_annotation (ty: Tac.term) (rng: Range.range) (ctx: list string): Tac.Tac unit =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_Unknown ->
    fail "error: term requires explicit type annotation" rng ctx
  | _ -> ()

let element_of_stream_ty (ty: Tac.term): Tac.Tac (option Tac.term) =
  // TODO: unify / match?
  let (hd, args) = Tac.collect_app ty in
  match Tac.inspect_unascribe hd, args with
  | Tac.Tv_FVar fv, ((elty, _) :: _) ->
    let fv' = Tac.inspect_fv fv in
    // TODO: check for @@stream_ctor_attr instead of by-name?
    if fv' = Ref.explode_qn (`%stream) // TermEq.term_eq hd (`stream)
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

let lift_prim (e: env) (prim: Tac.term): Tac.Tac (Tac.term & list Tac.term & Tac.term) =
  // TODO: unwrap prim: remove unwrap type arguments
  let ty = Tac.tc e.tac_env prim in
  let nm =
    match Tac.inspect_unascribe prim with
    | Tac.Tv_FVar fv ->
      let fv' = Tac.inspect_fv fv in
      (quote (Some fv'))
    | _ -> (`None)
  in
  let (args,res) = Tac.collect_arr ty in
  let res = PTB.returns_of_comp res in
  let ft =
    List.fold_right (fun a b -> (`Table.FTFun (Shallow.shallow (`#a)) (`#b))) args (`Table.FTVal (Shallow.shallow (`#res)))
  in
  // eta expand primitives, if necessary: this is necessary for treating lemmas as unit prims.
  // it also helps deal with an old, now-fixed, bug in F* normaliser where un-eta'd primops got bad types
  let prim = match Tac.inspect_unascribe prim with
    | Tac.Tv_Abs _ _ -> prim
    | _ -> PTB.eta_expand prim ty
  in
  (`liftP'prim (ShallowPrim.mkPrim (`#nm) (`#ft) (`#prim))), args, res

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
    | [] -> (`liftP'stream #(`#tret) (`#hd))
    | (tm,ty)::tms ->
      go_app (`liftP'apply #(`#ty) (`#hd) (`#tm)) tms
  in
  let abs = go_abs xmatch (List.rev ((nscrut, tscrut) :: List.map (fun (nm,_,_) -> (nm, tret)) nbrs)) in
  let abs, _, _ = lift_prim e abs in
  let app = go_app abs ((scrut, tscrut) :: List.map (fun (_,_,tm) -> (tm, tret)) nbrs) in
  app

let lift_ty: Tac.term -> Tac.Tac Tac.term =
  let rec go (t: Tac.term): Tac.Tac Tac.term =
    match Tac.inspect t with
    | Tac.Tv_FVar fv ->
      let fv' = Tac.inspect_fv fv in
      if fv' = Ref.explode_qn (`%stream)
      then (`Shallow.stream)
      else t
    | Tac.Tv_AscribedC e c topt use_eq ->
      // F* bug: visit_tm does not descend into computations
      let c = Tac.visit_comp go (Ref.pack_comp c) in
      Tac.pack (Tac.Tv_AscribedC e (Ref.inspect_comp c) topt use_eq)
    | _ -> t
  in Tac.visit_tm go

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
    let ty = Tac.tc e.tac_env t in
    let m  = mode_of_ty ty in
    debug_print (fun _ -> "fvar: " ^ Tac.term_to_string t ^ " mode: " ^ Tac.term_to_string (quote m) ^ " ty: " ^  Tac.term_to_string ty);
    (m, t)
  | Tac.Tv_Const (vc: Tac.vconst) ->
    (Static, t)

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let rec go_lifts m hd args argtys: Tac.Tac Tac.term = match m, args, argtys with
      | ModeFun _ false m2, (_,Ref.Q_Explicit)::_, _ :: argtys ->
        go_lifts m2 hd args argtys

      | _, (arg,Ref.Q_Meta _) :: _, _
      | _, (arg,Ref.Q_Implicit) :: _, _ ->
        fail "not supported: cannot lift implicit / meta applications"
          (Ref.range_of_term arg) ["go_lifts"]

      | ModeFun Static _  m2, (arg,_)::args, argty :: argtys ->
        let (ma, arg) = lift_tm e arg in
        let (ma, arg) = mode_cast Stream (ma, arg) in
        go_lifts m2 (`liftP'apply #(`#argty) (`#hd) (`#arg)) args argtys

      | Static, [], [] -> hd
      | _, _, _ ->
        fail ("cannot lift application! bad mode / args")
          (Ref.range_of_term t)
            ["mode: " ^ Tac.term_to_string (quote m);
            "args:"  ^ Tac.term_to_string (quote args);
            "argtys:"  ^ Tac.term_to_string (quote argtys);
            "hd:"  ^ Tac.term_to_string hd;
            "go_lifts"]
    in
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
          let prim, argtys, res = lift_prim e hd in
          (match argtys with
          | argty :: argtys ->
            let apps = go_lifts m2 (`liftP'apply #(`#argty) (`#prim) (`#arg)) args argtys in
            Stream, (`liftP'stream #(`#res) (`#apps))
          | [] -> fail "cannot apply primitive - type has no arguments" (Tac.range_of_term hd)
            ["head: " ^ Tac.term_to_string hd; "arg: " ^ Tac.term_to_string arg])
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
        Tac.pack (Tac.Tv_FVar (env_get_core_of_source fv e))
      | _ -> hd
    in
    debug_print (fun () -> "app hd: " ^ Tac.term_to_string hd ^ " mode: " ^ Tac.term_to_string (quote mh) ^ " ty: " ^  Tac.term_to_string (Tac.tc e.tac_env hd));
    // (static x) stops lifting of x, but if the result is applied to
    // another argument, we still want to lift that:
    // > lift ((static x) y) ==> x (lift y)
    if TermEq.term_eq hd (`static)
    then match args with
         | (hd, Ref.Q_Explicit)::args -> go_apps (mode_of_ty (Tac.tc e.tac_env hd)) hd args
         | (ty, Ref.Q_Implicit)::(hd, Ref.Q_Explicit)::args -> go_apps (mode_of_ty ty) hd args
         | _ -> fail "static: impossible: expected application" (Ref.range_of_term t) []
    else go_apps mh hd args
  | Tac.Tv_Abs bv tm ->
    // abstractions need explicit binders
    assert_type_annotation bv.sort (Ref.range_of_term t) ["in abstraction " ^ Tac.binder_to_string bv];
    debug_print (fun () -> "Abs: lift_tm with " ^ Tac.term_to_string bv.sort);
    let m1 = mode_of_ty bv.sort in
    let (m2, tm) = lift_tm (env_push bv m1 e) tm in
    (ModeFun m1 (PTB.qual_is_explicit bv.qual) m2, Tac.pack (Tac.Tv_Abs bv tm))

  | Tac.Tv_Let true attrs b def body ->
    debug_print (fun () -> "letrec: binder type: " ^ Tac.term_to_string (b.sort));
    let mdef = mode_of_ty b.sort in
    let e = env_push b mdef e in
    let (_mdef, def) = lift_tm e def in
    let (mb, body) = lift_tm e body in
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
        let bodyabs = Tac.pack (Tac.Tv_Abs b body) in
        Shallow.(`(let^) (`#def) (`#bodyabs))
      | _, _ -> Tac.pack (Tac.Tv_Let false attrs b def body)
    in
    (mb, lett)

  | Tac.Tv_Match scrut0 ret brs ->
    let (ms, scrut) = lift_tm e scrut0 in
    (match ms with
    | Static ->
      debug_print (fun () -> "match: static scrutinee " ^ Tac.term_to_string scrut);
      let mts = Tac.map (fun (pat,tm) -> lift_tm (env_push_pat pat Static e) tm) brs in
      let (mbrs, ts) = joins_modes (Ref.range_of_term t) mts in
      let brs = Pipit.List.zip2 (List.map fst brs) ts in
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
      let brs = Tac.map (fun (pat,tm) -> check_pat_top pat; (pat, go_stream e tm)) brs in

      // XXX: WRONG COMPLEXITY: this typechecking must be very bad for nested pattern matches
      let tscrut = element_of_stream_ty_force (Tac.tc e.tac_env scrut0) in
      let tret = match brs with
       | (_, tm) :: _ -> element_of_stream_ty_force (Tac.tc e.tac_env tm)
       | [] -> Tac.pack Tac.Tv_Unknown in
      debug_print (fun () -> "match: returns: " ^ Tac.term_to_string (quote ret));
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
    (mm, Tac.pack (Tac.Tv_AscribedT tm ty tac use_eq))

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
      (mm, Tac.pack (Tac.Tv_AscribedC tm (Tac.C_Total ty) tac use_eq))
      // TODO lemmas etc?
    | _ ->
      fail ("unsupported: type ascriptions on effects: " ^ Tac.comp_to_string cmp)
        (Ref.range_of_term t) [])

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ | Tac.Tv_Arrow  _ _ | Tac.Tv_Type   _
  | Tac.Tv_Refine _ _ | Tac.Tv_Unknown     -> (Static, t)

  | Tac.Tv_Unsupp ->
    fail ("lift failed: cannot inspect term: " ^ Tac.term_to_string t)
      (Ref.range_of_term t) ["(unsupported term)"]


let autolift_bind1 (e: env) (nm nm_core: string): Tac.Tac Tac.sigelt =
  let lb_src = PTB.lookup_lb_top e.tac_env (Ref.explode_qn nm) in

  let (m, core_def) = lift_tm e lb_src.lb_def in
  let core_def = lift_ty core_def in
  debug_print (fun () -> "lifted is: " ^ Tac.term_to_string core_def);

  // the source program might infer non-stream types for results etc; re-infer the type instead
  let ty = Tac.pack Tac.Tv_Unknown in
  // let (core_def, ty) =
  //   match Tac.tc_term e.tac_env core_def with
  //   | (None, _) -> (core_def, Tac.pack Tac.Tv_Unknown)
  //   | (Some (core_def, (_, ty)), _) -> (core_def, ty)
  // in

  // TODO: support recursive bindings
  let lb_core: Tac.letbinding = {
    lb_fv  = Tac.pack_fv (Ref.explode_qn nm_core);
    lb_us  = lb_src.lb_us;
    lb_typ = ty;
    lb_def = core_def;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let {isrec=false; lbs=[lb_core]} in
  let se: Tac.sigelt = Tac.pack_sigelt sv in
  let nm_src_const = Tac.pack (Tac.Tv_Const (Ref.C_String nm)) in
  let attrs = [`core; `of_source (`#nm_src_const)] in
  Ref.set_sigelt_attrs [] se

let autolift_binds (nms: list string): Tac.Tac (list Tac.sigelt) =
  let e = env_nil () in
  Tac.map (fun nm -> autolift_bind1 e nm (nm ^ "_core")) nms
