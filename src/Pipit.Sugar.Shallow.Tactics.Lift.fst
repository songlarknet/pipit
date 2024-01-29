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
  check whether two operations are equal. This is currently unimplemented.

  High-level question:
    * is this a massive hack? Should this use the new DSL framework instead?

  Implementation questions / limitations:
    * record constructors and record field accessors do not typecheck with FStar.Tactics.tc
    * mutual recursion isn't exposed by Tac.inspect. Exposing this would be a big change, wouldn't it?
*)
module Pipit.Sugar.Shallow.Tactics.Lift

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2

module TermEq = FStar.Reflection.V2.TermEq

module Range = FStar.Range

module List = FStar.List.Tot

#push-options "--print_implicits --print_full_names --ugly --print_bound_var_types"

let fail (#a: Type) (msg: string) (rng: Range.range) (ctx: list string): Tac.Tac a =
  let str0 = "Lift transform: failure at " ^ Tac.range_to_string rng ^ "\n  " ^ msg in
  let str = List.fold_left (fun str str' -> str ^ "\n    * " ^ str') str0 ctx in
  Tac.fail str

let range_of_term' (tm: Tac.term): Range.range = Ref.range_of_term tm

let rec zip2 (#x #y: Type) (xs: list x) (ys: list y): list (x & y)
  = match xs, ys with
  | x::xs, y::ys -> (x,y) :: zip2 xs ys
  | _ -> []


(*** Streaming public interface ***)

assume new type stream (a: eqtype)
type static (a: Type) = a

assume val return (#a: eqtype) (x: a): stream a

assume val fby (#a: eqtype) (x: a) (xs: stream a): stream a

(*** Lifting annotations exposed to user ***)
unfold
let as_static (#a: Type) (x: static a): static a = x

unfold
let as_stream (#a: eqtype) (x: stream a): stream a = x

(*** Internal stream combinators and inserted calls ***)
assume new type stream_app (a: Type)

assume val liftP'prim (#ft: Type) (f: ft): stream_app ft

assume val liftP'apply (#a: eqtype) (#ft: Type) (f: stream_app (a -> ft)) (ea: stream a): stream_app ft

assume val liftP'close (#a: eqtype) (ea: stream_app a): stream a


// assume val liftP'close_lemma (#p: prop) (f: stream_app (squash p)): stream unit
// assume val liftP'apply_lemma (#a: eqtype) (#ft: a -> prop) (f: stream_app ((xa: a) -> Lemma (ft a))) (ea: stream a): stream_app (ft a)

assume val rec' (#a: eqtype) (f: stream a -> stream a): stream a

assume val (let^) (#a #b: eqtype) (f: stream a) (g: stream a -> stream b): stream b

(*** Lift transform definitions ***)
let stream'name: Tac.name = ["Pipit"; "Sugar"; "Shallow"; "Tactics"; "Lift"; "stream"]
let static'name: Tac.name = ["Pipit"; "Sugar"; "Shallow"; "Tactics"; "Lift"; "static"]
let as_static'name: Tac.name = ["Pipit"; "Sugar"; "Shallow"; "Tactics"; "Lift"; "as_static"]

type mode = | Stream | Static | ModeFun: mode -> explicit: bool -> mode -> mode

let debug_print str = Tac.print str

noeq
type env = { tac_env: Tac.env; mode_env: list (nat & mode); }

let env_nil (): Tac.Tac env = { tac_env = Tac.top_env (); mode_env = []; }

let env_push (b: Tac.binder) (m: mode) (e: env): env =
  { tac_env  = Ref.push_namedv e.tac_env (Ref.pack_namedv b);
    mode_env = (b.uniq, m) :: e.mode_env }

let env_get_mode (b: Tac.namedv) (e: env) (rng: Range.range): Tac.Tac mode =
  match List.find (fun (uniq,m) -> uniq = b.uniq) e.mode_env with
  | None ->
    fail ("no such binder: b" ^ Tac.namedv_to_string b)
      rng []
  | Some (_, m) -> m

let rec env_push_pat (p: Tac.pattern) (m: mode) (e: env): Tac.Tac env =
  match p with
  | Tac.Pat_Constant _ -> e
  | Tac.Pat_Cons c ->
    Tac.fold_left (fun e (p,_) -> env_push_pat p m e) e c.subpats
  | Tac.Pat_Var v ->
    env_push (Tac.namedv_to_binder v.v (Tac.unseal v.sort)) m e
  | Tac.Pat_Dot_Term _ -> e


let assert_type_annotation (ty: Tac.term) (rng: Range.range) (ctx: list string): Tac.Tac unit =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_Unknown ->
    fail "error: term requires explicit type annotation" rng ctx
  | _ -> ()

let qual_is_explicit (q: Ref.aqualv): bool =
  match q with
  | Ref.Q_Explicit -> true
  | _ -> false

let rec mode_of_ty (ty: Tac.term): Tac.Tac mode =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_App tm (arg,aqual) ->
    (match Tac.inspect_unascribe tm with
    | Tac.Tv_FVar fv ->
      if Tac.inspect_fv fv = stream'name
      then Stream
      // else if Tac.inspect_fv fv = static'name
      // then Some Static
      else Static
    | _ -> Static)
  | Tac.Tv_Arrow arg (Tac.C_Total res)
  | Tac.Tv_Arrow arg (Tac.C_GTotal res)
  // We don't support general effects, but parse them anyway in case the effect is Tot
  | Tac.Tv_Arrow arg (Tac.C_Eff _ _ res _ _) ->
    ModeFun (mode_of_ty arg.sort) (qual_is_explicit arg.qual) (mode_of_ty res)
  | Tac.Tv_Arrow arg (Tac.C_Lemma _ _ _) ->
    ModeFun (mode_of_ty arg.sort) (qual_is_explicit arg.qual) Static
  | _ -> Static

let mode_join (rng: Range.range) (m1 m2: mode): Tac.Tac mode = match m1, m2 with
  | Stream, Static -> Stream
  | Static, Stream -> Stream
  | Static, Static -> Static
  | _, _ -> if m1 = m2 then m1 else fail ("cannot join incompatible modes: " ^ Tac.term_to_string (quote (m1, m2))) rng []

let mode_cast (m_expect: mode) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  (match mt, m_expect with
  | (Static, tm), Stream -> (Stream, (`return (`#tm)))
  | (m, tm), _ -> (m, tm))

let type_cast (ty: Tac.term) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  match Tac.inspect ty with
  | Tac.Tv_Unknown ->
    mt
  | _ ->
    (match mt, mode_of_ty ty with
    | (Static, tm), Stream -> (Stream, (`return (`#tm)))
    | _ -> mt)

let joins_modes (rng: Range.range) (mts: list (mode & Tac.term)): Tac.Tac (mode & list Tac.term) =
  match mts with
  | (m0, tm) :: mts' ->
    let ms' = List.map fst mts' in
    let m = Tac.fold_left (mode_join rng) m0 ms' in
    (m, Tac.map (fun x -> snd (mode_cast m x)) mts)
  | [] -> (Static, [])

let unwrap_AscribeT (tm: Tac.term): Tac.Tac Tac.term =
  match Tac.inspect tm with
  | Tac.Tv_AscribedT tm _ _ _ -> tm
  | _ -> tm

let lift_stream_match (scrut: Tac.term) (ret: option Tac.match_returns_ascription) (brs: list (Tac.pattern & Tac.term)): Tac.Tac Tac.term =
  let mk_namedv (pp: string) =
    { uniq = Tac.fresh (); sort = Tac.seal (`_); ppname = Ref.as_ppname pp } <: Tac.namedv
  in
  let nscrut = mk_namedv "scrut" in
  let nbrs = Tac.map (fun (pat,tm) ->
    (mk_namedv "branch", pat, tm)) brs in
  let brs = List.map (fun (nm,pat,tm) -> (pat, Tac.pack (Tac.Tv_Var nm))) nbrs in
  let xmatch = Tac.pack (Tac.Tv_Match (Tac.pack (Tac.Tv_Var nscrut)) ret brs) in
  let rec go_abs hd nms: Tac.Tac Tac.term = match nms with
    | [] -> hd
    | nm::nms ->
      go_abs (Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder nm (`_)) hd)) nms
  in
  let rec go_app hd tms: Tac.Tac Tac.term = match tms with
    | [] -> (`liftP'close (`#hd))
    | tm::tms ->
      go_app (`liftP'apply (`#hd) (`#tm)) tms
  in
  let abs = go_abs xmatch (List.rev (nscrut :: List.map (fun (nm,_,_) -> nm) nbrs)) in
  let app = go_app (`liftP'prim (`#abs)) (scrut :: List.map (fun (_,_,tm) -> tm) nbrs) in
  app

(* get mode of type-annotated function body; requires type annotations
  This doesn't take an environment as it's used to compute the environment
  for the letrec subexpressions *)
let rec mode_of_letrec (t: Tac.term): Tac.Tac mode =
  match Tac.inspect t with
  | Tac.Tv_Const (vc: Tac.vconst) ->
    Static

  | Tac.Tv_Abs bv tm ->
    // abstractions need explicit binders
    assert_type_annotation bv.sort (range_of_term' t) ["abstraction " ^ Tac.binder_to_string bv; "in letrec (mode_of_letrec)"];
    let m1 = mode_of_ty bv.sort in
    let m2 = mode_of_letrec tm in
    ModeFun m1 (qual_is_explicit bv.qual) m2

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    mode_of_ty ty

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    (match cmp with
    | Tac.C_Total ty | Tac.C_GTotal ty ->
      mode_of_ty ty
    | Tac.C_Lemma _ _ _ -> Static
    | Tac.C_Eff _ _ _ _ _ ->
      fail ("unsupported effect: " ^ Tac.comp_to_string cmp) (range_of_term' t) ["in letrec (mode_of_letrec)"])
  | _ ->
    fail "letrecs must have explicit type annotations"
      (range_of_term' t)
      ["in letrec (mode_of_letrec)"]

let rec descend (e: env) (t: Tac.term): Tac.Tac (mode & Tac.term) =
  let go_stream (e: env) (t: Tac.term) =
    let (m, t) = descend e t in
    match m with
    | Static -> (`return (`#t))
    | Stream -> t
    | ModeFun _ _ _ ->
      fail ("cannot lift function to stream: " ^ Tac.term_to_string t)
        (range_of_term' t)
        []
  in
  match Tac.inspect t with
  | Tac.Tv_Var (v: Tac.namedv) ->
    (env_get_mode v e (range_of_term' t), t)
  | Tac.Tv_BVar (v: Tac.bv) ->
    fail
      ("unexpected bvar; expected named variables only " ^ Tac.term_to_string t)
      (range_of_term' t) []
  | Tac.Tv_FVar (v: Tac.fv) ->
    (mode_of_ty (Tac.tc e.tac_env t), t)
  | Tac.Tv_Const (vc: Tac.vconst) ->
    (Static, t)

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let rec go_lifts m hd args: Tac.Tac (mode & Tac.term) = match m, args with
      | ModeFun _ false m2, (_,Ref.Q_Explicit)::_ ->
        go_lifts m2 hd args

      | _, (arg,Ref.Q_Meta _) :: _
      | _, (arg,Ref.Q_Implicit) :: _ ->
        fail "not supported: cannot lift implicit / meta applications"
          (range_of_term' arg) ["go_lifts"]

      | ModeFun Static _  m2, (arg,_)::args ->
        let (ma, arg) = descend e arg in
        let (ma, arg) = mode_cast Stream (ma, arg) in
        go_lifts m2 (`liftP'apply (`#hd) (`#arg)) args

      | Static, [] -> (Stream, (`liftP'close (`#hd)))
      | _, _ ->
        fail ("cannot lift application! bad mode / args")
          (range_of_term' t)
            ["mode: " ^ Tac.term_to_string (quote m);
            "args:"  ^ Tac.term_to_string (quote args);
            "hd:"  ^ Tac.term_to_string hd;
            "go_lifts"]
    in
    let rec go_apps m hd args: Tac.Tac (mode & Tac.term) = match m, args with
      | ModeFun _ false m2, (_,Ref.Q_Explicit)::_ ->
        go_apps m2 hd args

      | ModeFun m1 mq m2, (arg,aq)::args ->
        let (ma, arg) = descend e arg in
        (match ma, m1 with
        | Stream, Static ->
          (match aq with
          | Ref.Q_Explicit -> ()
          | _ ->
            fail "cannot lift implicit arguments - put all implicit arguments before explicits, or rearrange the arguments with a lambda (TODO)."
              (range_of_term' arg)
              ["go_apps"]
            );
          go_lifts m2 (`liftP'apply (liftP'prim (`#hd)) (`#arg)) args
        | _, _ ->
          let (ma, arg) = mode_cast m1 (ma, arg) in
          go_apps m2 (Tac.pack (Tac.Tv_App hd (arg, aq))) args)

      | _, (arg,_) :: _ ->
        fail "too many arguments for mode"
          (range_of_term' arg)
          ["go_apps"]
      | _, [] -> (m, hd)
    in
    let (hd, args) = Tac.collect_app t in
    let (mh, hd) = descend e hd in
    // (as_static x) stops lifting of x, but if the result is applied to
    // another argument, we still want to lift that:
    // > lift ((as_static x) y) ==> x (lift y)
    if TermEq.term_eq hd (`as_static)
    then match args with
         | (hd, Ref.Q_Explicit)::args -> go_apps (mode_of_ty (Tac.tc e.tac_env hd)) hd args
         | (ty, Ref.Q_Implicit)::(hd, Ref.Q_Explicit)::args -> go_apps (mode_of_ty ty) hd args
         | _ -> fail "as_static: impossible: expected application" (range_of_term' t) []
    else go_apps mh hd args
  | Tac.Tv_Abs bv tm ->
    // abstractions need explicit binders
    assert_type_annotation bv.sort (range_of_term' t) ["in abstraction " ^ Tac.binder_to_string bv];
    debug_print ("Abs: descend with " ^ Tac.term_to_string bv.sort);
    let m1 = mode_of_ty bv.sort in
    let (m2, tm) = descend (env_push bv m1 e) tm in
    (ModeFun m1 (qual_is_explicit bv.qual) m2, Tac.pack (Tac.Tv_Abs bv tm))

  | Tac.Tv_Let true attrs b def body ->
    debug_print ("letrec: binder type: " ^ Tac.term_to_string (b.sort));
    // Letrec: recursive streams do not have lambdas; recursive functions do
    (match Tac.inspect def with
    | Tac.Tv_Abs _ _ ->
      debug_print ("descending into fun-letrec: " ^ Tac.term_to_string def);
      let mdef = mode_of_letrec def in
      let e = env_push b mdef e in
      let (_mdef, def) = descend e def in
      let (mb, body) = descend e body in
      (mb, Tac.pack (Tac.Tv_Let true attrs b def body))
    | _ ->
      debug_print ("stream-letrec: " ^ Tac.term_to_string def);
      let e = env_push b Stream e in
      let def = go_stream e def in
      let body = go_stream e body in
      let defabs = Tac.pack (Tac.Tv_Abs b def) in
      let bodyabs = Tac.pack (Tac.Tv_Abs b body) in

      (Stream, (`(let^) (rec' (`#defabs)) (`#bodyabs))))
  | Tac.Tv_Let false attrs b def body ->
    let (md, def) = descend e def in
    let (md, def) = type_cast b.sort (md,def) in
    let (mb, body) = descend (env_push b md e) body in
    let lett = match md, mb with
      | Stream, Stream ->
        // HACK: remove unit type annotation from let-bindings: the parser
        // generates `let x: unit = ... in ...` for semicolons.
        // we want to lift this to a stream of units, but generally we want
        // to leave user-written type annotations alone.
        let b = if TermEq.term_eq b.sort (`unit)
          then { b with sort = (`stream unit) } <: Tac.simple_binder
          else b
        in
        let bodyabs = Tac.pack (Tac.Tv_Abs b body) in
        (`(let^) (`#def) (`#bodyabs))
      | _, _ -> Tac.pack (Tac.Tv_Let false attrs b def body)
    in
    (mb, lett)

  | Tac.Tv_Match scrut ret brs ->
    // HACK: remove type ascriptions from match scrutinees: the parser
    // generates if-expressions with the form `match x <: bool with ...`
    // but this doesn't work if we lift the scrutinee to a stream.
    // Maybe we should convert the type ascription to `x <: stream bool`
    let scrut = unwrap_AscribeT scrut in
    let (ms, scrut) = descend e scrut in
    (match ms with
    | Static ->
      debug_print ("match: static scrutinee " ^ Tac.term_to_string scrut);
      let mts = Tac.map (fun (pat,tm) -> descend (env_push_pat pat Static e) tm) brs in
      let (mbrs, ts) = joins_modes (range_of_term' t) mts in
      let brs = zip2 (List.map fst brs) ts in
      (mbrs, Tac.pack (Tac.Tv_Match scrut ret brs))
    | Stream ->
      debug_print ("match: stream scrutinee " ^ Tac.term_to_string scrut);
      // XXX: the current semantics for streaming-matches is more of a "select"
      // than a match: all of the branches are eagerly evaluated, and then we
      // just choose which to return based on the scrutinee
      let rec check_pat p: Tac.Tac unit = match p with
        | Tac.Pat_Constant _ -> ()
        | Tac.Pat_Cons c -> Tac.iter (fun (p,_) -> check_pat p) c.subpats
        | Tac.Pat_Var _ ->
          fail ("streaming patterns can't bind variables (TODO)")
            (range_of_term' t) ["in pattern-match"]
        // not sure what this means...
        | Tac.Pat_Dot_Term _ -> ()
      in
      let check_pat_top p: Tac.Tac unit = match p with
        // TODO: assert Pat_Var binder is `_` / not mentioned
        | Tac.Pat_Var _ -> ()
        | p -> check_pat p
      in
      let brs = Tac.map (fun (pat,tm) -> check_pat_top pat; (pat, go_stream e tm)) brs in
      (Stream, lift_stream_match scrut ret brs)
    | ModeFun _ _ _ ->
      fail "match scrutinee cannot be function"
        (range_of_term' scrut) ["in pattern match"])

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    debug_print ("AscribedT: " ^ Tac.term_to_string ty);
    let (mm, tm) = descend e tm in
    let (mm, tm) = type_cast ty (mm, tm) in
    (mm, Tac.pack (Tac.Tv_AscribedT tm ty tac use_eq))

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    (match cmp with
    | Tac.C_Total ty ->
      debug_print ("AscribedC: " ^ Tac.term_to_string ty);
      let (mm, tm) = descend e tm in
      let (mm, tm) = type_cast ty (mm, tm) in
      (mm, Tac.pack (Tac.Tv_AscribedC tm cmp tac use_eq))
      // TODO lemmas etc?
    | _ ->
      fail ("unsupported: type ascriptions on effects: " ^ Tac.comp_to_string cmp)
        (range_of_term' t) [])

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ -> (Static, t)
  | Tac.Tv_UInst (v: Tac.fv) (us: Tac.universes) -> (Static, t)
  | Tac.Tv_Arrow  bv c -> (Static, t)
  | Tac.Tv_Type   u    -> (Static, t)
  | Tac.Tv_Refine b r  -> (Static, t)
  | Tac.Tv_Unknown     -> (Static, t)

  | Tac.Tv_Unsupp ->
    fail ("lift failed: cannot inspect term: " ^ Tac.term_to_string t)
      (range_of_term' t) ["(unsupported term)"]


let tac_lift (t: Tac.term): Tac.Tac Tac.term =
  debug_print ("term is: " ^ Tac.term_to_string t);
  let e = env_nil () in
  let (mm, t') = descend e t in
  debug_print ("lifted is: " ^ Tac.term_to_string t');
  // TC required to instantiate uvars?
  // ignore (Tac.recover (fun () -> Tac.tc e.tac_env t'));
  t'

(*** Examples / test cases ***)

// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// [@@Tac.preprocess_with tac_lift]
// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y


// // local function bindings require explicit type annotations
// [@@Tac.preprocess_with tac_lift]
// let eg_letrecfun (x: int): int =
//   let rec count (x: int): int = if x > 0 then count (x - 1) else 0 in
//   count 0

// [@@Tac.preprocess_with tac_lift]
// let eg_letrec (x: stream int): stream int =
//   let rec count = 0 `fby` count + 1 in
//   let y = (0 <: stream int) in
//   // let z: stream int = 0 in
//   // let rec count (i: int): int = count i in
//   (1 + y) + count

// [@@Tac.preprocess_with tac_lift]
// let eg_pairs (x: stream int): stream int =
//   0 `fby` fst (x, x)


// type ctor = | Ctor: x: int -> y: int -> ctor
// [@@Tac.preprocess_with tac_lift]
// let eg_ctor (add: stream int): stream ctor =
//   let rec rcd =
//     let x = 0 `fby` Ctor?.x rcd + add in
//     let y = 0 `fby` Ctor?.y rcd - add in
//     Ctor x y
//   in
//   rcd

// [@@Tac.preprocess_with tac_lift]
// let eg_pairsrec (add: stream int): stream (int & int) =
//   let rec xy =
//     let x = 0 `fby` fst xy + add in
//     let y = 0 `fby` snd xy - add in
//     (x, y)
//   in
//   xy


// [@@Tac.preprocess_with tac_lift]
// let eg_let (x: stream int): stream int =
//   let y = (x + 1, x - 1)
//   in
//   let z = fst y in
//   let rec count (x: int): int = if x > 0 then count (x - 1) else x in
//   count z

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match (x: stream int): stream int =
//   let abs =
//     match x >= 0 with
//       | true -> x
//       | false -> -x
//   in abs

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_if (x: stream int): stream int =
//   let abs =
//     if x >= 0 then x else -x
//   in abs


// [@@Tac.preprocess_with tac_lift]
// let eg_static_match (consts: list int) (x: stream int): stream int =
//   match consts with
//   | [] -> 0
//   | c::_ -> c + x


(*** Not supported examples ***)
// mutual recursion not supported:

// [@@Tac.preprocess_with tac_lift]
// let eg_letrec_mut (x: int): int =
//   let rec a = x + b
//       and b = x - a
//   in a

// streaming matches cannot bind variables:

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match x with
//   | Some e -> e
//   | None -> 0

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_letmatch (xy: stream (int & int)): stream int =
//   let (x, y) = xy in
//   x + y

// should work, but doesn't:
// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bool (x: stream int): stream bool =
//   match x >= 0 with
//     | true -> false
//     | xr -> xr


// fails: cannot typecheck record accessors?

// type record = { x: int; y: int; }
// [@@Tac.preprocess_with tac_lift]
// let eg_record (add: stream int): stream int =
//   let rec rcd =
//     let x = 0 `fby` rcd.x + add in
//     let y = 0 `fby` rcd.y - add in
//     {x; y}
//   in
//   rcd
