(* box/lift transform *)
module Pipit.Sugar.Shallow.Tactics.Lift

// module PPT = Pipit.Prim.Table
// module PPS = Pipit.Prim.Shallow
// module SB  = Pipit.Sugar.Base
// module SSB = Pipit.Sugar.Shallow.Base

module RefV1 = FStar.Reflection.V1
module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2

module List = FStar.List.Tot

// #push-options "--print_implicits --print_full_names --ugly"

type stream (a: eqtype) = nat -> a

[@@"opaque_to_smt"]
let rec'
  (f: stream 'a -> stream 'a): stream 'a =
  (fun ix ->
    f (admit ()) ix)

[@@"opaque_to_smt"]
let (let^) (f: stream 'a) (g: stream 'a -> stream 'b): stream 'b =
    g f

[@@"opaque_to_smt"]
let return (#a: eqtype) (x: a): stream a = (fun ix -> x)

unfold
let nolift (#a: eqtype) (x: a): a = x

unfold
let lift (#a: eqtype) (x: stream a): stream a = x

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

let stream_ty_unify_get_elt (e: env) (ty: Tac.term): Tac.Tac Tac.term =
  let uvar = Tac.uvar_env e.tac_env (Some (`eqtype)) in
  let expect = (`stream (`#uvar)) in
  if Tac.unify_env e.tac_env ty expect
  then uvar
  else Tac.fail ("expected stream type; got type " ^ Tac.term_to_string ty)


let mode_of_ty (e: env) (ty: Tac.term): Tac.Tac (mode & Tac.term) =
  match Tac.inspect_unascribe ty with
  | Tac.Tv_App tm (arg,aqual) ->
    (match Tac.inspect_unascribe tm with
    | Tac.Tv_FVar fv ->
      if Tac.inspect_fv fv = ["Pipit"; "Sugar"; "Shallow"; "Tactics"; "Lift"; "stream"]
      then (debug_print ("here: " ^ Tac.term_to_string ty); (Stream, arg))
      else (Pure, ty)
    | _ -> (Pure, ty))
  | _ -> (Pure, ty)

let mode_of_ty' (e: env) (ty: Tac.term): Tac.Tac mode =
  fst (mode_of_ty e ty)


// let unify_mode_of_ty (e: env) (ty: Tac.term): Tac.Tac (mode & Tac.term) =
//   // XXX: optimisation: inspect / pattern match without generating fresh var?
//   let uvar = Tac.uvar_env e.tac_env (Some (`eqtype)) in
//   let expect = (`stream (`#uvar)) in
//   if Tac.match_env e.tac_env ty expect
//   then (Stream, uvar)
//   else (ignore (Tac.unify_env e.tac_env uvar (`unit)); (Pure, ty))

// let unify_mode_of_ty' (e: env) (ty: Tac.term): Tac.Tac mode =
//   fst (unify_mode_of_ty e ty)

let mode_join (m1 m2: mode): mode = match m1, m2 with
  | Stream, _ -> Stream
  | _, Stream -> Stream
  | Pure, Pure -> Pure

let mode_opt_join (m1 m2: option mode): option mode = match m1, m2 with
  | None, _ -> m2
  | _, None -> m1
  | Some Stream, _ -> Some Stream
  | _, Some Stream -> Some Stream
  | Some Pure, Some Pure -> Some Pure

let modes_of_arr (e: env) (ty: Tac.term): Tac.Tac (option (list mode & mode)) =
  match Tac.collect_arr ty with
  | args, Tac.C_Total res ->
    // TODO: avoid unification?
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
    Tac.fail ("Lift.descend: unexpected bvar? " ^ Tac.term_to_string t)
  | Tac.Tv_FVar (v: Tac.fv) ->
    (mode_of_ty' e (Tac.tc e.tac_env t), t)
  | Tac.Tv_Const (vc: Tac.vconst) ->
    (Pure, t)

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let rec mk_pure_apps hd args: Tac.Tac Tac.term = match args with
      | (mm,arg,aqual)::args -> mk_pure_apps (Tac.pack (Tac.Tv_App hd (arg,aqual))) args
      | [] -> hd
    in
    let rec mk_lift_apps hd args: Tac.Tac Tac.term = match args with
    //TODO DO LIFT
      | (mm,arg,aqual)::args -> mk_lift_apps (Tac.pack (Tac.Tv_App hd (arg,aqual))) args
      | [] ->
        debug_print "TODO:LIFT!";
      hd
    in
    let rec go_lifts hd args m collect: Tac.Tac (mode & Tac.term) = match args with
      | (arg,aqual)::args ->
        let (mm,arg) = descend e arg in
        go_lifts hd args (mode_join mm m) ((mm,arg,aqual) :: collect)
      | [] ->
        (match m with
        | Pure -> (Pure, mk_pure_apps hd (List.rev collect))
        | Stream -> (Stream, mk_lift_apps hd (List.rev collect)))
    in
    let rec mk_apps hd modes args: Tac.Tac Tac.term = match modes, args with
      | mx::modes, (arg,aqual)::args ->
        let (ma, arg) = descend e arg in
        // XXX: is tc here necessary?
        let (ma, arg) = mode_cast e mx (Tac.tc e.tac_env arg) (ma, arg) in
        mk_apps (Tac.pack (Tac.Tv_App hd (arg, aqual))) modes args
      | _, _ -> hd
    in
    let rec go_apps hd args: Tac.Tac (mode & Tac.term) = match Tac.inspect hd with
      | Tac.Tv_FVar (v: Tac.fv) ->
        let ty = Tac.tc e.tac_env hd in
        (match modes_of_arr e ty with
        | None -> go_lifts hd args Pure []
        | Some (modes, ret) -> (ret, mk_apps hd modes args))
      | Tac.Tv_Var (v: Tac.namedv) ->
        Tac.fail "TODO: local functions not supported yet"
      | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
        go_apps hd ((arg, aqual) :: args)
      | _ ->
        Tac.fail ("Lift.descend: expected application head; got term " ^ Tac.term_to_string hd)
    in
    go_apps hd [(arg, aqual)]
  | Tac.Tv_Abs bv tm ->
    debug_print ("Abs: descend with " ^ Tac.term_to_string bv.sort);
    let (mt, tm) = descend (env_push bv (mode_of_ty' e bv.sort) e) tm in
    (mt, Tac.pack (Tac.Tv_Abs bv tm))

  | Tac.Tv_Uvar _ _ -> (Pure, t)

  | Tac.Tv_Let true attrs b def body ->
    debug_print ("letrec: binder type: " ^ Tac.term_to_string (b.sort));
    // Letrec: recursive streams do not have lambdas; recursive functions do
    (match Tac.inspect def with
    | Tac.Tv_Abs _ _ ->
      Tac.fail "NOT SUPPORTED: fun letrecs"
      // debug_print ("descending into fun-letrec: " ^ Tac.term_to_string def);
      // let e = env_push b Pure e in
      // let (md, def) = descend e None def in
      // let (mb, body) = descend e m body in
      // (mode_join md mb, Tac.pack (Tac.Tv_Let true attrs b def body))
    | _ ->
      debug_print ("stream-letrec: " ^ Tac.term_to_string def);
      // let elty = stream_ty_unify_get_elt e b.sort in
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
      | Stream ->
        // let elty = stream_ty_unify_get_elt e b.sort in
        (`(let^) (`#def) (`#bodyabs))
    in
    (mode_join md mb, lett)

  | Tac.Tv_Match scrut ret brs ->
    //TODO: only lift matches with no binders to start with
    (Pure, t)

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



// [@@Tac.preprocess_with tac_lift]
// let pp_letrecfun (x: int): int =
//   let rec count x = if x > 0 then count (x - 1) else 0 in
//   count 0

[@@Tac.preprocess_with tac_lift]
let pp_letrec (x: stream int): stream int =
  let rec count: stream int = count in // if count > 0 then count else 0 in
  let y = (0 <: stream int) in
  // let z: stream int = 0 in
  // let rec count (i: int): int = count i in
  1 + y + count

// [@@Tac.preprocess_with tac_lift]
// let pp_pairs (x: stream int): stream (int & int) =
//   (x, x)


// [@@Tac.preprocess_with tac_lift]
// let pp_let (x: stream int): stream int =
  // let y: stream (int & int) = (x + 1, x - 1)
  // in
  // let z: stream int = fst y in
  // let rec count x = count x + 1 in
  // Tac.print "hello";
  // z

// [@@Tac.preprocess_with lift]
// let pp_letop (x: int): int =
//   let^ y: int = x + 1
//   in y

// [@@Tac.preprocess_with lift]
// let pp_letrec_fun (x: int): int =
//   let rec a z = if z >= 0 then x else a (z - 1)
//   in a x

// [@@Tac.preprocess_with lift]
// let pp_letrec_strm (x: int): int =
//   let rec a = x + a
//   in a

// [@@Tac.preprocess_with lift]
// let pp_letrec_mut (x: int): int =
//   let rec a = x + b
//       and b = x - a
//   in a
