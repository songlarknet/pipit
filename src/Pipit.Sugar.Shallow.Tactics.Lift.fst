(* box/lift transform *)
module Pipit.Sugar.Shallow.Tactics.Lift

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2

module List = FStar.List.Tot

// #push-options "--print_implicits --print_full_names --ugly"

(*** Streaming public interface ***)

assume new type stream (a: eqtype)

assume val return (#a: eqtype) (x: a): stream a

assume val fby (#a: eqtype) (x: a) (xs: stream a): stream a

(*** Lift annotations exposed to user ***)
unfold
let unlifted (#a: eqtype) (x: a): a = x

unfold
let lifted (#a: eqtype) (x: stream a): stream a = x

(*** Internal stream combinators and inserted calls ***)
assume new type stream_app (a: Type)

assume val liftP'prim (#ft: Type) (f: ft): stream_app ft

assume val liftP'apply (#a: eqtype) (#ft: Type) (f: stream_app (a -> ft)) (ea: stream a): stream_app ft

assume val liftP'close (#a: eqtype) (ea: stream_app a): stream a

assume val rec' (#a: eqtype) (f: stream a -> stream a): stream a

assume val (let^) (#a #b: eqtype) (f: stream a) (g: stream a -> stream b): stream b

(*** Lift ***)
let stream'name: Tac.name = ["Pipit"; "Sugar"; "Shallow"; "Tactics"; "Lift"; "stream"]
let unlifted'name: Tac.name = ["Pipit"; "Sugar"; "Shallow"; "Tactics"; "Lift"; "unlifted"]


type mode = | Stream | Pure

let debug_print str = Tac.print str

noeq
type env = { tac_env: Tac.env; mode_env: list (nat & mode); }

let env_nil (): Tac.Tac env = { tac_env = Tac.top_env (); mode_env = []; }

let env_push (b: Tac.binder) (m: mode) (e: env): env =
  { tac_env  = Ref.push_namedv e.tac_env (Ref.pack_namedv b);
    mode_env = (b.uniq, m) :: e.mode_env }

let env_get_mode (b: Tac.namedv) (e: env): Tac.Tac mode =
  match List.find (fun (uniq,m) -> uniq = b.uniq) e.mode_env with
  | None -> Tac.fail ("no such binder: b" ^ Tac.namedv_to_string b)
  | Some (_, m) -> m

let assert_type_annotation (ty: Tac.term) (err: string): Tac.Tac unit =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_Unknown ->
    Tac.fail ("Lift.descend: error: requires explicit type annotation: " ^ err)
  | _ -> ()


let mode_of_ty (e: env) (ty: Tac.term): Tac.Tac (mode & Tac.term) =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_App tm (arg,aqual) ->
    (match Tac.inspect_unascribe tm with
    | Tac.Tv_FVar fv ->
      if Tac.inspect_fv fv = stream'name
      then (debug_print ("here: " ^ Tac.term_to_string ty); (Stream, arg))
      else (Pure, ty)
    | _ -> (Pure, ty))
  | _ -> (Pure, ty)

let mode_of_ty' (e: env) (ty: Tac.term): Tac.Tac mode =
  fst (mode_of_ty e ty)

let mode_join (m1 m2: mode): mode = match m1, m2 with
  | Stream, _ -> Stream
  | _, Stream -> Stream
  | Pure, Pure -> Pure

let modes_of_arr (e: env) (ty: Tac.term): Tac.Tac (option (list mode & mode)) =
  match Tac.collect_arr ty with
  | args, Tac.C_Total res ->
    let margs = Tac.map (mode_of_ty' e) args in
    let mres = mode_of_ty' e res in
    if List.existsb (fun m -> m = Stream) (mres::margs)
    then Some (margs, mres)
    else None
  | _ -> None


let mode_cast (e: env) (m_expect: mode) (ty: Tac.term) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  (match mt, m_expect with
  | (Pure, tm), Stream -> (Stream, (`return #(`#ty) (`#tm)))
  | (m, tm), _ -> (m, tm))

let type_cast (e: env) (ty: Tac.term) (mt: mode & Tac.term): Tac.Tac (mode & Tac.term) =
  match Tac.inspect ty with
  | Tac.Tv_Unknown ->
    mt
  | _ ->
    (match mt, mode_of_ty e ty with
    | (Pure, tm), (Stream, elty) -> (Stream, (`return #(`#elty) (`#tm)))
    | _ -> mt)

let rec descend (e: env) (t: Tac.term): Tac.Tac (mode & Tac.term) =
  let go_stream (e: env) (t: Tac.term) (elty: Tac.term) =
    snd (mode_cast e Stream elty (descend e t))
  in
  // Tac.compress?
  // debug_print ("Inspecting term " ^ Tac.term_to_string t);
  // debug_print (match m with | None -> "None" | Some Stream -> "Some Stream" | Some Pure -> "Some Pure");
  match Tac.inspect t with
  | Tac.Tv_Var (v: Tac.namedv) ->
    (env_get_mode v e, t)
  | Tac.Tv_BVar (v: Tac.bv) ->
    Tac.fail ("Lift.descend: unexpected bvar; expected named variables only " ^ Tac.term_to_string t)
  | Tac.Tv_FVar (v: Tac.fv) ->
    // DISALLOW: ensure no unapplied functions?
    (mode_of_ty' e (Tac.tc e.tac_env t), t)
  | Tac.Tv_Const (vc: Tac.vconst) ->
    (Pure, t)

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let rec mk_pure_apps hd args: Tac.Tac Tac.term = match args with
      | (mm,arg,aqual)::args -> mk_pure_apps (Tac.pack (Tac.Tv_App hd (arg,aqual))) args
      | [] -> hd
    in
    let rec mk_lift_apps hd args: Tac.Tac Tac.term = match args with
      | (mm,arg,aqual)::args ->
        // CHECK: ensure fully applied? partial-applications will fail as no stream instance
        let (mm, arg) = mode_cast e Stream (Tac.pack Tac.Tv_Unknown) (mm, arg) in
        mk_lift_apps (`liftP'apply (`#hd) (`#arg)) args
      | [] ->
        hd
    in
    let rec go_lifts hd args m collect: Tac.Tac (mode & Tac.term) = match args with
      | (arg,Tac.Q_Explicit)::args ->
        let (mm,arg) = descend e arg in
        go_lifts hd args (mode_join mm m) ((mm,arg,aqual) :: collect)
      | (arg,aqual)::args ->
        Tac.fail ("Lift.descend: cannot lift implicit arguments: " ^ Tac.term_to_string arg)
      | [] ->
        (match m with
        | Pure -> (Pure, mk_pure_apps hd (List.rev collect))
        | Stream ->
          let hd = (`liftP'prim (`#hd)) in
          (Stream, `liftP'close (`#(mk_lift_apps hd (List.rev collect)))))
    in
    let rec mk_apps hd modes args: Tac.Tac Tac.term = match modes, args with
      | mx::modes, (arg,aqual)::args ->
        let (ma, arg) = descend e arg in
        let (ma, arg) = mode_cast e mx (Tac.pack Tac.Tv_Unknown) (ma, arg) in
        mk_apps (Tac.pack (Tac.Tv_App hd (arg, aqual))) modes args
      | _, _ -> hd
    in
    let (hd, args) = Tac.collect_app t in
    (match Tac.inspect hd with
      | Tac.Tv_FVar (v: Tac.fv) ->
        // XXX: this fails for record accessors, and lookup_typ returns None
        let ty = Tac.tc e.tac_env hd in
        if Tac.inspect_fv v = unlifted'name
        then (mode_of_ty' e ty, t)
        else
          (match modes_of_arr e ty with
          | None -> go_lifts hd args Pure []
          | Some (modes, ret) -> (ret, mk_apps hd modes args))
      | Tac.Tv_Var (v: Tac.namedv) ->
        let ty = Tac.tc e.tac_env hd in
        assert_type_annotation ty (Tac.namedv_to_string v);
        (match modes_of_arr e ty with
        | None -> go_lifts hd args Pure []
        | Some (modes, ret) -> (ret, mk_apps hd modes args))
      | _ ->
        Tac.fail ("Lift.descend: expected application head; got term " ^ Tac.term_to_string hd))
  | Tac.Tv_Abs bv tm ->
    // abstractions need explicit binders
    assert_type_annotation bv.sort (Tac.binder_to_string bv);
    debug_print ("Abs: descend with " ^ Tac.term_to_string bv.sort);
    let (m, tm) = descend (env_push bv (mode_of_ty' e bv.sort) e) tm in
    // lambdas are pure, but we can't lift them to streams
    (Pure, Tac.pack (Tac.Tv_Abs bv tm))


  | Tac.Tv_Let true attrs b def body ->
    debug_print ("letrec: binder type: " ^ Tac.term_to_string (b.sort));
    // Letrec: recursive streams do not have lambdas; recursive functions do
    (match Tac.inspect def with
    | Tac.Tv_Abs _ _ ->
      // TODO: need to track function modes in environment
      Tac.fail "NOT SUPPORTED: fun letrecs"
      // debug_print ("descending into fun-letrec: " ^ Tac.term_to_string def);
      // // the bound function must be Pure, as streams can't hold functions
      // let e = env_push b Pure e in
      // let (_pure, def) = descend e def in
      // let (mb, body) = descend e body in
      // (mb, Tac.pack (Tac.Tv_Let true attrs b def body))
    | _ ->
      debug_print ("stream-letrec: " ^ Tac.term_to_string def);
      let e = env_push b Stream e in
      let def = go_stream e def (Tac.pack Tac.Tv_Unknown) in
      let body = go_stream e body (Tac.pack Tac.Tv_Unknown) in
      let defabs = Tac.pack (Tac.Tv_Abs b def) in
      let bodyabs = Tac.pack (Tac.Tv_Abs b body) in

      (Stream, (`(let^) (rec' (`#defabs)) (`#bodyabs))))
  | Tac.Tv_Let false attrs b def body ->
    let (md, def) = descend e def in
    let (md, def) = type_cast e b.sort (md,def) in
    let (mb, body) = descend (env_push b md e) body in
    // cast body if md=Stream and mb=Pure; should only happen if b not mentioned
    let (mb, body) = match md, mb with
      | Stream, Pure -> Stream, (`return (`#body))
      | _ -> md, body
    in
    let bodyabs = Tac.pack (Tac.Tv_Abs b body) in
    let lett = match md with
      | Pure -> Tac.pack (Tac.Tv_Let false attrs b def body)
      | Stream -> (`(let^) (`#def) (`#bodyabs))
    in
    (mode_join md mb, lett)

  | Tac.Tv_Match scrut ret brs ->
    let (ms, scrut) = descend e scrut in
    (match ms with
    | Pure ->
      let rec go_pure brs: Tac.Tac (mode & list Tac.branch) = match brs with
        | [] -> (Pure, [])
        | (pat,tm) :: brs ->
          let (m,brs) = go_pure brs in
          let (mt,tm) = descend e tm in
          (mode_join m mt, (pat,tm) :: brs)
      in
      let (mb, brs) = go_pure brs in
      (mb, Tac.pack (Tac.Tv_Match scrut ret brs))
    | Stream ->
      let rec go_stream brs: Tac.Tac (mode & list Tac.branch) = match brs with
        | [] -> (Pure, [])
        | (pat,tm) :: brs ->
          let (m,brs) = go_stream brs in
          let (mt,tm) = descend e tm in
          (mode_join m mt, (pat,tm) :: brs)
      in
      let (mb, brs) = go_stream brs in
      (mb, Tac.pack (Tac.Tv_Match scrut ret brs)))

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    debug_print ("AscribedT: " ^ Tac.term_to_string ty);
    let (mm, tm) = descend e tm in
    let (mm, tm) = type_cast e ty (mm, tm) in
    (mm, Tac.pack (Tac.Tv_AscribedT tm ty tac use_eq))

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    (match cmp with
    | Tac.C_Total ty ->
      debug_print ("AscribedC: " ^ Tac.term_to_string ty);
      let (mm, tm) = descend e tm in
      let (mm, tm) = type_cast e ty (mm, tm) in
      (mm, Tac.pack (Tac.Tv_AscribedC tm cmp tac use_eq))
      // TODO lemmas etc?
    | _ -> Tac.fail "unsupported: type ascriptions on effects")

  // Type stuff: leave alone
  | Tac.Tv_Uvar _ _ -> (Pure, t)
  | Tac.Tv_UInst (v: Tac.fv) (us: Tac.universes) -> (Pure, t)
  | Tac.Tv_Arrow  bv c -> (Pure, t)
  | Tac.Tv_Type   u    -> (Pure, t)
  | Tac.Tv_Refine b r  -> (Pure, t)
  | Tac.Tv_Unknown     -> (Pure, t)

  | Tac.Tv_Unsupp ->
    Tac.fail ("lift failed: cannot inspect " ^ Tac.term_to_string t)


let tac_lift (t: Tac.term): Tac.Tac Tac.term =
  debug_print ("term is: " ^ Tac.term_to_string t);
  let e = env_nil () in
  let (mm, t') = descend e t in
  debug_print ("lifted is: " ^ Tac.term_to_string t');
  // TC required to instantiate uvars?
  // ignore (Tac.recover (fun () -> Tac.tc e.tac_env t'));
  t'

let fst (#a #b: eqtype): (a & b) -> a = fst


// do not support local function bindings yet
// [@@Tac.preprocess_with tac_lift]
// let eg_letrecfun (x: int): int =
//   let rec count x = if x > 0 then count (x - 1) else 0 in
//   count 0

[@@Tac.preprocess_with tac_lift]
let eg_letrec (x: stream int): stream int =
  let rec count = 0 `fby` count + 1 in
  let y = (0 <: stream int) in
  // let z: stream int = 0 in
  // let rec count (i: int): int = count i in
  (1 + y) + count

[@@Tac.preprocess_with tac_lift]
let eg_pairs (x: stream int): stream int =
  0 `fby` fst (x, x)


type ctor = | Ctor: x: int -> y: int -> ctor
[@@Tac.preprocess_with tac_lift]
let eg_ctor (add: stream int): stream ctor =
  let rec rcd =
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

[@@Tac.preprocess_with tac_lift]
let eg_pairsrec (add: stream int): stream (int & int) =
  let rec xy =
    // let (x,y) = xy in
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y)
  in
  xy

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


// [@@Tac.preprocess_with tac_lift]
// let eg_let (x: stream int): stream int =
  // let y: stream (int & int) = (x + 1, x - 1)
  // in
  // let z: stream int = fst y in
  // let rec count x = count x + 1 in
  // Tac.print "hello";
  // z

// [@@Tac.preprocess_with lift]
// let eg_letop (x: int): int =
//   let^ y: int = x + 1
//   in y

// [@@Tac.preprocess_with lift]
// let eg_letrec_fun (x: int): int =
//   let rec a z = if z >= 0 then x else a (z - 1)
//   in a x

// [@@Tac.preprocess_with lift]
// let eg_letrec_strm (x: int): int =
//   let rec a = x + a
//   in a

// [@@Tac.preprocess_with lift]
// let eg_letrec_mut (x: int): int =
//   let rec a = x + b
//       and b = x - a
//   in a
