(*

  Assumptions / limitations:
    * streams cannot be refined (not allowed: `ints: s int { forall i. ints `nth` i >= 0 }`)
    * refinement types must be declared at top level (not allowed: `s (x: int { x >= 0 })`)
    * variables are either fully stream or fully const
*)
module Pipit.Sugar.Shallow.Tactics

module PPS = Pipit.Prim.Shallow
module SB  = Pipit.Sugar.Base
module SSB = Pipit.Sugar.Shallow.Base

module Ref = FStar.Reflection.V2
module Tac = FStar.Tactics.V2

module List = FStar.List.Tot

open FStar.Tactics.NamedView

let norm_term (e: Ref.env) (tm: Ref.term): Tac.Tac Ref.term =
  // XXX what norm options?
  Tac.norm_term_env e [delta; primops] tm

#set-options "--print_full_names --ugly"


let rec lift_prim_go (args: list Tac.binder) (app: Ref.term): Tac.Tac Ref.term =
  match args with
  | bv :: args ->
    (match bv.qual with
    | Ref.Q_Explicit ->
      // let sort = Tac.pack (Tv_App (`SSB.s (`#bv.sort)) 
      //   (Tac.pack Tv_Unknown, Ref.Q_Meta (`Tactics.Typeclasses.tcresolve))
      //   ) in
      // let strm_wit_sort = (`SSB.has_stream (`#bv.sort)) in
      // let wit_uvar = Tac.uvar_env (Tac.top_env ()) (Some strm_wit_sort) in
      // Tac.unshelve wit_uvar;
      // Tactics.Typeclasses.tcresolve ();
      // let sort = (`SSB.s_explicit (`#bv.sort) (`#wit_uvar)) in
      // let bvv  = {bv with sort = sort; uniq = Tac.fresh () } in
      // let arg: Tac.bv = { index = List.length args; sort = FStar.Sealed.seal sort; ppname = bv.ppname } in
      // let arg = Tac.pack (Tv_BVar arg) in
      // let app = (`SB.liftP'app (`#app) (`#arg)) in
      let app = lift_prim_go args app in
      // let app = Tv_Abs bvv app in
      // let app = Tv_Abs bin_strm_wit app in
      Tac.pack app
    | Ref.Q_Implicit ->
      Tac.fail "implicit"
    | Ref.Q_Meta mm ->
      Tac.fail ("meta not supported sorry" ^ Tac.term_to_string mm))
  | [] -> (`SB.liftP'apps (`#app))

let lift_prim (nm: string) (tm: Ref.term): Tac.Tac Tac.decls =
  let e       = Tac.top_env () in
  let ty      = Tac.tc e tm in
  let ty      = norm_term e ty in
  let (bs,cmp)= Tac.collect_arr_bs ty in
  let tm_lift = tm in
  let tm_lift = Tac.pack (Tv_App (Tac.pack (Tv_FVar (Tac.pack_fv [`%SB.liftP'prim]))) (tm, Ref.Q_Explicit)) in
  // let tm_lift = (`SB.liftP'prim (`#tm)) in
  let tm_lift = lift_prim_go bs tm_lift in
  Tac.print ("term is: " ^ Tac.term_to_string tm_lift);
  // let ty_lift = Tac.tc e tm_lift in

  let lb      = {
    lb_fv = Tac.pack_fv List.(Tac.cur_module () @ [nm]);
    lb_us = [];
    lb_typ = (Tac.pack Tv_Unknown);
    lb_def = tm_lift;
  } in
  let sv: Tac.sigelt_view = Tac.Sg_Let {isrec=false; lbs=[lb]} in
  let ses: list Tac.sigelt = [Tac.pack_sigelt sv] in
  ses


let plus (i j: bool) = i && j
// let plus (a: eqtype) {| SSB.has_stream a |} (i j: int) = i + j


%splice[] (lift_prim "plus_lift" (`plus))

type mode = | Pure | Stream

// noeq
// type envs = {
//   pure: Ref.env;
//   real: Ref.env;
// }
(*
noeq
type config = {
  // stream_ctor_fvs: list Ref.fv;
  stream_ctor_names: list Ref.name;
}

let mk_config (e: Ref.env): Tac.Tac config =
  // TODO: go through environment, ensure that any occurrences of stream types are tagged with is_stream_attr or something.
  // maybe we could imagine that `stream` has a separate kind `stream: eqtype -> mode` that disallows it from occurring inside types, only at top-level function definitions.
  let stream_ctor_fvs   = Ref.lookup_attr (`SB.stream_ctor_attr) e in
  let stream_ctor_names = List.map Ref.inspect_fv stream_ctor_fvs in
  { stream_ctor_names; }

noeq
type res = {
  tm:      Ref.term;
  ty_pure: Ref.typ;
  ty:      Ref.typ;
  md:      mode;
}


let get_fv_ty (e: Ref.env) (fv: Tac.fv): Tac.Tac Ref.typ =
  let nm = (Ref.inspect_fv fv) in
  match Ref.lookup_typ e nm with
  | Some sg ->
    (match Tac.inspect_sigelt sg with
    | Tac.Sg_Let lets ->
      // MISSING? it would be nice to get the attributes here too, but I can't figure out how to get it
      let lb = Tac.lookup_lb lets.lbs nm in
      lb.lb_typ
    | Tac.Sg_Val view -> view.typ
    | _ -> Tac.fail ("Cannot find definition for free variable " ^ Ref.fv_to_string fv))
  | _ -> Tac.fail ("Cannot find definition for free variable " ^ Ref.fv_to_string fv)

let rec ty_stream_ctor_head (cfg: config) (e: Ref.env) (ty: Ref.typ): Tac.Tac bool =
  match Tac.inspect_unascribe ty with
  | Tv_FVar fv | Tv_UInst fv _ -> List.mem (Ref.inspect_fv fv) cfg.stream_ctor_names
  | Tv_App hd _ -> ty_stream_ctor_head cfg e hd
  | _ -> false

let rec ty_stream_ctor_free (cfg: config) (e: Ref.env) (ty: Ref.typ): Tac.Tac bool =
  match Tac.inspect_unascribe ty with
  | Tv_FVar fv | Tv_UInst fv _ -> List.mem (Ref.inspect_fv fv) cfg.stream_ctor_names
  | Tv_App hd (arg, _) ->
    if ty_stream_ctor_free cfg e hd then true else ty_stream_ctor_free cfg e arg
  | Tv_Arrow bv (Ref.C_Total t) ->
    if ty_stream_ctor_free cfg e bv.sort then true else ty_stream_ctor_free cfg e t
  | _ -> false


let ret_pure (e: Ref.env) (tm: Ref.term) =
  let ty = Tac.tc e tm in
  { tm = tm; ty_pure = ty; ty = ty; md = Pure }

let mk_stream_return (tm: Ref.term): Ref.term =
  (`SSB.const (`#tm))

let rec mk_stream_prim_ty_ft (ty: Ref.typ): Tac.Tac Ref.typ =
  // TODO: use arity of application to force unfolding...
  match Tac.inspect_unascribe ty with
  | Tv_Arrow a (Ref.C_Total b) ->
    let b = mk_stream_prim_ty_ft b in
    (`SSB.p'ftfun (`#a) (`#b))
  | _ -> (`SSB.p'ftval (`#ty))

let mk_stream_prim_ty (e: Ref.env) (fv: Tac.fv): Tac.Tac (Ref.typ & string) =
  let ty = get_fv_ty e fv in
  // MISSING? cannot normalise type here, because universe names are opened by Ref.lookup_typ but aren't bound in environment. how to add universes to environment?
  // Tac.norm_binding_type?
  // let ty = tac_norm e ty in
  (mk_stream_prim_ty_ft ty, Tac.term_to_string ty)

let mk_stream_prim (e: Ref.env) (fv: Tac.fv): Tac.Tac Ref.term =
  let (ty, ty_id) = mk_stream_prim_ty e fv in
  let nm          = Ref.inspect_fv fv in
  let id          = [Tac.fv_to_string fv; ":"; ty_id] in
  let id          = quote id in
  let sem         = Tac.pack (Tv_FVar fv) in
  (`PPS.mkPrim (Some (`#(id))) (`#ty) (`#sem))

// let mk_stream_app (e: Ref.env) (fv: Tac.fv): Tac.Tac Ref.term =
  

let _ =
  assert (true) by (
    let e = Tac.cur_env () in
    let fv = Ref.pack_fv ["PipitRuntime";"Prim";"p'select"] in
    Tac.print (Tac.term_to_string (mk_stream_prim e fv)))



// let rec lift_app (e: Ref.env) (tm: Ref.term): Tac.Tac res =
//   match Tac.inspect_unascribe tm with



// let rec lift_term (e: envs) (tm: Ref.term): Tac.Tac res =
//   match Tac.inspect_unascribe tm with
//   | Tv_Var (v: namedv) ->
//     Tac.print ("Tv_Var " ^ Tac.term_to_string tm);
//     // let u = env_lookup e.pure v
//     ret_pure e tm
//   | Tv_BVar (v: bv) ->
//     Tac.print ("Tv_BVar " ^ Tac.term_to_string tm);
//     ret_pure e tm
//   | Tv_FVar (v: Tac.fv) ->
//     Tac.print ("Tv_FVar " ^ Tac.term_to_string tm);
//     ret_pure e tm
//   | Tv_App hd (arg, Ref.Q_Explicit) ->
//     // Tac.print ("Tv_App hd:" ^ Tac.term_to_string hd);
//     ignore (lift_term e hd);
//     ignore (lift_term e arg);
//     ret_pure e tm
//   // | Tv_App hd (arg, Ref.Q_Implicit) ->
//     //TODO

//     // let xs = Tac.collect_app tm in
//     // descend
//     // ret_pure e tm
//   | Tv_Abs bv body ->
//     // TODO: descend; for now, assume pure
//     ret_pure e tm

//   | Tv_Let is_rec attrs b def body ->
//   // | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
//     Tac.print "let";
//     ignore (lift_term e def);
//     ignore (lift_term e body);
//     ret_pure e tm

//   | Tv_Match scrut ret brs ->
//   // | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> named_term_view
//     ret_pure e tm

//   // Types and universes should not have streaming operations
//   | Tv_UInst _ _
//   | Tv_Arrow _ _
//   | Tv_Type _
//   | Tv_Refine _ _
//   //
//   | Tv_Const _
//   | Tv_Uvar _ _ ->
//     ret_pure e tm
//   // TODO: use type ascriptions
//   // | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> named_term_view
//   // | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> named_term_view

//   // unkowns and unsupporteds should probably fail
//   // | Tv_Unknown | Tv_Unsupp | Tv_AscribedT _ _ _ _ | Tv_AscribedC _ _ _ _ ->
//   | _ ->
//     Tac.fail ("lift_term: cannot translate term: " ^ Tac.term_to_string tm)

// type tup = {x: int; y: int; }

// let test (): tup =


//   synth (fun () ->
//     let env = Tac.cur_env () in
//     let ee = { pure = env; real = env; } in
//     let tm' = lift_term ee (`(
//       let rec xy =
//         let x = 0 + 1 in
//         let y = x + 1 in
//         { x; y }
//       in { y = xy.x; x = xy.y }
//     )) in
//     Tac.print ("term: " ^ Tac.term_to_string tm'.tm);
//     Tac.exact tm'.tm
//   )



// type triggers = { trigger_index: nat; trigger_new: bool; }
// type s (a: eqtype) = a
// let fby (#a: eqtype) (p1 p2: a) = p1

// let trigger (reset_ck advance_ck: s bool): s triggers =
//   let rec tr =
//     let trigger_index = 0 `fby` tr.trigger_index + (if advance_ck then 1 else 0) in
//     let trigger_new   = trigger_index <> (0 `fby` trigger_index) in
//     { trigger_index; trigger_new; }
//   in
//   tr

// // once `let rec ... and ...` is supported by Tac.inspect:
// let trigger (reset_ck advance_ck: s bool): s triggers =
//   let rec trigger_index = 0 `fby` trigger_index + (if advance_ck then 1 else 0)
//   and     trigger_new   = trigger_index <> (0 `fby` trigger_index)
//   in { trigger_index; trigger_new; }






//////////// exploration

// open FStar.Tactics.V2
// module UInt8 = FStar.UInt8

// let constant_list (name: string) (l: list UInt8.t): Tac decls =
//   let len = FStar.List.length l in
//   let t = `(FStar.List.llist UInt8.t (`@len)) in
//   let fv = pack_fv (cur_module () @ [ name ]) in
//   let lb = ({lb_fv=fv; lb_us=[]; lb_typ=t; lb_def = quote l}) in
//   let se = pack_sigelt (Sg_Let {isrec=false;lbs=[lb]}) in
//   [se]

// %splice[] (constant_list "l1" [ 1uy ])
// %splice[] (constant_list "l2" [ 1uy; 2uy; 3uy; 99uy ])

// module T = FStar.Tactics.V2

// let pipit_let (nm: string) (t: term) =
//   // T.set_options "--lax";
//   // let t = `(fun (i: nat) -> i) in
//   let ty = T.tc (T.top_env ()) t in
//   let lb = {lb_fv = T.pack_fv (cur_module () @ [nm]);
//                       lb_us = [];
//                       lb_typ = `(nat -> nat);
//                       lb_def = `(fun (i: nat) -> i)} in
//   let sv : T.sigelt_view = T.Sg_Let {isrec=false; lbs=[lb]} in
//   let ses : list T.sigelt = [T.pack_sigelt sv] in
//   T.dump "here";
//   ses

// // val fir: nat -> int

// %splice[fir] (pipit_let "fir" (`(fun (x: nat) -> assert (x > 0); x)))

// let test () =
//   assert (fir == fir) by (T.norm [delta]; T.dump "X")
*)