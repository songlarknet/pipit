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

let mode_of_ty (e: Tac.env) (ty: Tac.term): Tac.Tac (mode & Tac.term) =
  // XXX: optimisation: inspect / pattern match without generating fresh var?
  let uvar = Tac.uvar_env e (Some (`eqtype)) in
  let expect = (`stream (`#uvar)) in
  if Tac.match_env e ty expect
  then (Stream, uvar)
  else (ignore (Tac.unify_env e uvar (`unit)); (Pure, ty))

let mode_of_ty' (e: Tac.env) (ty: Tac.term): Tac.Tac mode =
  fst (mode_of_ty e ty)

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

let try_return (e: Tac.env) (m: option mode) (t: Tac.term): Tac.Tac (mode & Tac.term) =
  let ty = Tac.tc e t in
  match (m, mode_of_ty e ty) with
  | None, (m', _) -> (m', t)
  | Some Pure, (Pure, _) -> (Pure, t)
  | Some Pure, (Stream, _) -> Tac.fail ("Expected pure expression; got stream term ``" ^ Tac.term_to_string t ^ "'' of type ``" ^ Tac.term_to_string ty ^ "''")
  | Some Stream, (Pure, ty') ->
    debug_print ("lift-return: " ^ Tac.term_to_string t);
    (Stream, (`return #(`#ty') (`#t)))
  | Some Stream, (Stream, _) -> (Stream, t)

let rec descend (e: Tac.env) (m: option mode) (t: Tac.term): Tac.Tac (mode & Tac.term) =
  let push (bv: Tac.binder): Tac.env = Ref.push_namedv e (Ref.pack_namedv bv) in
  let go (t: Tac.term) = descend e m t in
  let try_tc () =
    let ty = Tac.tc e t in
    debug_print ("Term " ^ Tac.term_to_string t ^ " has type: " ^ Tac.term_to_string ty);
    t
  in
  // Tac.compress?
  // debug_print ("Inspecting term " ^ Tac.term_to_string t);
  // debug_print (match m with | None -> "None" | Some Stream -> "Some Stream" | Some Pure -> "Some Pure");
  match Tac.inspect t with
  | Tac.Tv_Var (v: Tac.namedv) ->
    try_return e m t
  | Tac.Tv_BVar (v: Tac.bv) ->
    Tac.print "WARN: Lift.descend: unexpected bvar?";
    try_return e m t
  | Tac.Tv_FVar (v: Tac.fv) ->
    try_return e m t
  | Tac.Tv_Const (vc: Tac.vconst) ->
    try_return e m t

  | Tac.Tv_App (hd: Tac.term) (arg, aqual) ->
    let (mh, hd) = go hd in
    let (ma, arg) = go arg in
    (mode_join mh ma, Tac.pack (Tac.Tv_App hd (arg, aqual)))
  | Tac.Tv_Abs bv tm ->
    let (mt, tm) = descend (push bv) m tm in
    (mt, Tac.pack (Tac.Tv_Abs bv tm))

  | Tac.Tv_Uvar _ _ -> (Pure, t)

  | Tac.Tv_Let true attrs b def body ->
    debug_print ("letrec: binder type: " ^ Tac.term_to_string (b.sort));
    // Letrec: recursive streams do not have lambdas; recursive functions do
    (match Tac.inspect def with
    | Tac.Tv_Abs _ _ ->
      debug_print ("descending into fun-letrec: " ^ Tac.term_to_string def);
      let e = push b in
      let (md, def) = descend e None def in
      let (mb, body) = descend e m body in
      (mode_join md mb, Tac.pack (Tac.Tv_Let true attrs b def body))
    | _ ->
      debug_print ("stream-letrec: " ^ Tac.term_to_string def);
      let bsort = (`stream _) in
      let e = push ({ b with sort = bsort }) in
      let (md, def) = descend e (Some Stream) def in
      let (mb, body) = descend e (Some Stream) body in
      let defabs = Tac.pack (Tac.Tv_Abs b def) in
      let bodyabs = Tac.pack (Tac.Tv_Abs b body) in

      (Stream, (`(let^) (rec' (`#defabs)) (`#bodyabs))))
  | Tac.Tv_Let false attrs b def body ->
    let m' = match m with
      | None -> None
      | Some Stream -> None
      | Some Pure -> Some Pure
    in
    let (md, def) = descend e m' def in
    let (mb, body) = descend (push b) m body in
    let bodyabs = Tac.pack (Tac.Tv_Abs b body) in
    let lett = match md with
      | Pure -> Tac.pack (Tac.Tv_Let false attrs b def body)
      | Stream -> (`(let^) (`#def) (`#bodyabs))
    in
    (mode_join md mb, lett)

  | Tac.Tv_Match scrut ret brs ->
  //TODO: only lift matches with no binders to start with
    (Pure, t)

  | Tac.Tv_AscribedT (tm: Tac.term) (ty: Tac.term) tac use_eq ->
    debug_print ("AscribedT: " ^ Tac.term_to_string ty);
    let mm = mode_of_ty' e ty in
    let (mm, tm) = descend e (Some mm) tm in
    (mm, Tac.pack (Tac.Tv_AscribedT tm ty tac use_eq))

  | Tac.Tv_AscribedC (tm: Tac.term) (cmp: Tac.comp) tac use_eq ->
    let mm = match cmp with
      | Tac.C_Total ty ->
        mode_of_ty' e ty
        // TODO?
      | _ -> Tac.fail "unsupported: type ascriptions on effects"
    in
    let (mm, tm) = descend e (Some mm) tm in
    (mm, Tac.pack (Tac.Tv_AscribedC tm cmp tac use_eq))

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
  let e = Tac.top_env () in
  let (mm, t') = descend e (Some Stream) t in
  debug_print ("lifted is: " ^ Tac.term_to_string t');
  ignore (Tac.tc e t');
  t'

let fst (#a #b: eqtype): (a & b) -> a = fst

[@@Tac.preprocess_with tac_lift]
let pp_letrec (x: stream int): stream int =
  let rec count: stream int = x in
  let z: stream int = count in
  // let rec count (i: int): int = count i in
  0

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
