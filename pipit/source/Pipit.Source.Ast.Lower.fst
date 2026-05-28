(* Lower a `Pipit.Source.Ast.ast` to a checked core expression over the
   shallow primitive table (`Pipit.Prim.Shallow.table`).

   Stage A — tactic-driven term builder. `lower` returns a quoted F*
   term that, after splicing and re-typechecking, has type:

     exp Pipit.Prim.Shallow.table ctx rty

   (`exp`, not `cexp`, for now — blessing to `cexp` is left to the
   splice site so that we can iterate on Lower without paying for
   `check_all` discharge on every change.)

   The Lower pass is specialised to `Pipit.Prim.Shallow.table`. If/when
   another backend table is needed, a sibling module under
   `Pipit.Source.Ast.Lower.*` can target it, sharing the same AST.

   Strategy
   --------
   * Lower is split into two mutually recursive helpers:
       `lower_stream` — produces an `exp t c ty`
       `lower_static` — produces a static F* term of the source type
     so each case knows what it's emitting.
   * `Stream` binders live in the cexp context (de Bruijn). `AVar n Stream`
     resolves to `XBVar idx` where `idx` is the number of stream binders
     between `n` and the innermost binding.
   * `Static` binders live as ordinary F* term variables (`namedv`).
     `AVar n Static` resolves to a `Tv_Var` of the stored `namedv`.
   * When a static value is consumed in stream context, it is lifted via
     `XVal`. Going the other way (stream -> static) is a hard error.
*)
module Pipit.Source.Ast.Lower

module T   = FStar.Tactics.V2
module R   = FStar.Reflection.V2
module L   = FStar.List.Tot

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface
module PPS = Pipit.Prim.Shallow
module PPT = Pipit.Prim.Table
module PXB = Pipit.Exp.Base
module PM  = Pipit.Prop.Metadata
module PSSB = Pipit.Prim.HasStream

(*** Lowering environment ***)

(* How a binder was introduced. *)
noeq
type binder_kind =
  (* Bound in the cexp context. Its de Bruijn index is recovered by
     counting the number of `BStream` binders that came after it. *)
  | BStream
  (* Bound as a real F* term variable at the splice site. *)
  | BStatic: nv: T.namedv -> binder_kind

noeq
type binder = {
  b_name: Ast.name;
  b_sty:  Ast.sty;
  b_kind: binder_kind;
}

(* Lowering environment: binders in scope (innermost first), plus an
   `inst_for` callback used to materialise `has_stream` typeclass
   instances for source types. The callback is supplied by the splice
   driver (`Pipit.Plugin.Lift`) so that polymorphic source bindings can
   thread local instance binders into the spliced term without relying
   on F*'s implicit-uvar machinery (which loses the local env for
   sigelts built via `Tv_App`/quasi-quote). Returning `None` falls back
   to the quasi-quote `PSSB.shallow sty` form (works for ground types). *)
noeq
type lower_env = {
  binders: list binder;
  inst_for: T.term -> T.Tac (option T.term);
}

let empty_env: lower_env = {
  binders = [];
  inst_for = (fun _ -> None);
}

let env_push (b: binder) (env: lower_env): lower_env =
  { env with binders = b :: env.binders }

(* Compute the de Bruijn index of a stream-bound name. Returns `None`
   if the name isn't a stream binder or isn't in scope. *)
let rec env_bvar_index (n: Ast.name) (bs: list binder): option nat =
  match bs with
  | [] -> None
  | b :: bs' ->
    if b.b_name = n
    then (match b.b_kind with | BStream -> Some 0 | _ -> None)
    else
      (match env_bvar_index n bs' with
       | None -> None
       | Some i ->
         (match b.b_kind with
          | BStream -> Some (i + 1)
          | BStatic _ -> Some i))

(* Look up a binder by name. *)
let rec env_lookup (n: Ast.name) (bs: list binder): option binder =
  match bs with
  | [] -> None
  | b :: bs' -> if b.b_name = n then Some b else env_lookup n bs'

(* Extract just the stream binders' source types from an env binder
   list, preserving innermost-first order. Used to build a caller-side
   cexp context when calling another lifted binding. *)
let rec stream_ctx_of_binders (bs: list binder): list Ast.sty =
  match bs with
  | [] -> []
  | b :: rest ->
    (match b.b_kind with
     | BStream -> b.b_sty :: stream_ctx_of_binders rest
     | BStatic _ -> stream_ctx_of_binders rest)

(*** Term builders ***)

(* Build the shallow type term for a source type: `PSSB.shallow #ty`.
   Relies on typeclass resolution at splice time to pick the right
   `has_stream` instance. Works for ground types (`int`, `bool`, ...)
   because F* resolves them globally regardless of env. For
   type-variable / polymorphic uses where the instance must come from a
   local binder, the caller must provide the instance term explicitly
   (see `shallow_ty_with_inst` and `Pipit.Plugin.Lift.instance_for`). *)
let shallow_ty (sty: Ast.sty): T.term = `PSSB.shallow (`#sty)

(* Like `shallow_ty`, but with the `has_stream` typeclass instance
   provided explicitly as `inst`. Built as raw `Tv_App` so no implicit
   uvar is created — important when the instance is a local binder
   whose scope F* would otherwise lose track of. *)
let shallow_ty_with_inst (sty: Ast.sty) (inst: T.term): T.term =
  let shallow_fv: T.term =
    T.pack (T.Tv_FVar (T.pack_fv ["Pipit"; "Prim"; "HasStream"; "shallow"])) in
  let applied: T.term = T.pack (T.Tv_App shallow_fv (sty, T.Q_Explicit)) in
  T.pack (T.Tv_App applied (inst, T.Q_Implicit))

(* Build a `shallow sty` term using `env.inst_for` when possible. *)
let shallow_ty_for_env (env: lower_env) (sty: Ast.sty): T.Tac T.term =
  match env.inst_for sty with
  | Some inst -> shallow_ty_with_inst sty inst
  | None      -> shallow_ty sty

let exp_XVal  (v: T.term): T.term =
  `(PXB.XBase #PPS.table (PXB.XVal #PPS.table (`#v)))

let exp_XBVar (i: T.term): T.term =
  `(PXB.XBase #PPS.table (PXB.XBVar #PPS.table (`#i)))

let exp_XLet  (sty: T.term) (def: T.term) (body: T.term): T.term =
  `(PXB.XLet #PPS.table (`#sty) (`#def) (`#body))

let exp_XMu   (body: T.term): T.term =
  `(PXB.XMu #PPS.table (`#body))

let exp_XFby  (v: T.term) (e: T.term): T.term =
  `(PXB.XFby #PPS.table (`#v) (`#e))

let exp_XCheck (e: T.term): T.term =
  `(PXB.XCheck #PPS.table PM.PSUnknown (`#e))

(* Compute the FQN of a lifted source binding's `__core_*` sigelt by
   replacing the last segment `nm` with `nm ^ "_core"`. Mirrors
   `Pipit.Plugin.Lift.env_core_nm`. *)
let core_fqn_of (src: Ast.fqn): T.Tac Ast.fqn =
  match L.rev src with
  | [] -> T.fail "Pipit.Source.Ast.Lower: empty FQN for lifted call"
  | nm :: rest -> L.rev ((nm ^ "_core") :: rest)

(* Build a typed F* list term `[e1; e2; ...] : list elem_ty`. The
   element type is needed so that nil/cons disambiguate; here we use it
   to build a `list shallow_type` for cexp contexts. *)
let rec list_term (elem_ty: T.term) (xs: list T.term): T.term =
  match xs with
  | [] -> `([] <: list (`#elem_ty))
  | x :: rest ->
    let tail = list_term elem_ty rest in
    `((`#x) :: (`#tail))

(* Shallow context (innermost first) for a list of source types in
   innermost-first order. *)
let context_term (env: lower_env) (sty_innermost_first: list Ast.sty): T.Tac T.term =
  let elem_ty: T.term = `Pipit.Prim.Shallow.shallow_type in
  list_term elem_ty (T.map (shallow_ty_for_env env) sty_innermost_first)

(* Wrap a body with a chain of XLets. `defs_innermost_first` lists the
   (sty, def) pairs in the order they were bound, innermost first
   (i.e. `[(t_n, a_n); ...; (t_1, a_1)]`), so the outermost XLet binds
   the first source argument and the innermost binds the last. *)
let rec wrap_xlets (env: lower_env) (defs_innermost_first: list (Ast.sty & T.term)) (body: T.term): T.Tac T.term =
  match defs_innermost_first with
  | [] -> body
  | (sty, def) :: rest ->
    let sh = shallow_ty_for_env env sty in
    let inner = exp_XLet sh def body in
    wrap_xlets env rest inner

(* Build a `funty shallow_type` term from argument and return source
   types: `FTFun a1 (FTFun a2 ... (FTVal r)) ...`. *)
let rec funty_of (env: lower_env) (arg_tys: list Ast.sty) (ret_ty: Ast.sty): T.Tac T.term =
  match arg_tys with
  | [] -> let r = shallow_ty_for_env env ret_ty in `(PPT.FTVal (`#r))
  | a :: rest ->
    let tail = funty_of env rest ret_ty in
    let sh = shallow_ty_for_env env a in
    `(PPT.FTFun (`#sh) (`#tail))

(* Build a `PPS.prim` record: `PPS.mkPrim id ft fn`. The `id` is wrapped
   as `Some s` / `None`. *)
let shallow_prim (env: lower_env) (id: option Ast.name) (arg_tys: list Ast.sty) (ret_ty: Ast.sty) (fn: T.term): T.Tac T.term =
  let id_tm: T.term =
    match id with
    | Some s -> `(Some (`#(T.pack (T.Tv_Const (T.C_String s)))))
    | None   -> `None
  in
  let ft_tm = funty_of env arg_tys ret_ty in
  `(PPS.mkPrim (`#id_tm) (`#ft_tm) (`#fn))

let exp_XPrim (p_tm: T.term): T.term =
  `(PXB.XPrim #PPS.table (`#p_tm))

let exp_XApp  (f: T.term) (a: T.term): T.term =
  `(PXB.XApp #PPS.table (`#f) (`#a))

let exp_XApps (e: T.term): T.term =
  `(PXB.XApps #PPS.table (`#e))

let int_const (i: int): T.term =
  T.pack (T.Tv_Const (T.C_Int i))

(* Allocate a fresh named variable of the given F* type and pretty name. *)
let fresh_nv (ppname: string) (ty: T.term): T.Tac T.namedv =
  { uniq = T.fresh (); sort = T.seal ty; ppname = R.as_ppname ppname }

(*** Entry points ***)

val lower_stream (env: lower_env) (a: Ast.ast): T.Tac T.term

val lower_static (env: lower_env) (a: Ast.ast): T.Tac T.term

let rec lower_stream env a =
  match a with
  | Ast.ALit _r lit ->
    exp_XVal lit.Ast.lit_tm

  | Ast.AVar _r n m ->
    (match m with
     | PPI.Stream ->
       (match env_bvar_index n env.binders with
        | Some i -> exp_XBVar (int_const i)
        | None -> T.fail ("Pipit.Source.Ast.Lower: stream variable not in scope: " ^ n))
     | PPI.Static ->
       (* Static values are lifted into stream context via XVal. *)
       let v_tm = lower_static env a in
       exp_XVal v_tm
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: unexpected functional mode on AVar: " ^ n))

  | Ast.APrim _r am p args ->
    (match am with
     | Ast.AppPureStream ->
       (* XApps (XApp (... (XApp (XPrim p) a1) ...) an) *)
       let prim_tm  = shallow_prim env p.Ast.prim_id p.Ast.prim_arg_tys p.Ast.prim_ret_ty p.Ast.prim_fn in
       let head     = exp_XPrim prim_tm in
       let arg_tms  = T.map (lower_stream env) args in
       let applied  = L.fold_left exp_XApp head arg_tms in
       exp_XApps applied
     | Ast.AppPureConst ->
       (* Static-only application; lift the resulting value into stream
          context via XVal. *)
       let v_tm = lower_static env a in
       exp_XVal v_tm)

  | Ast.ACallStream _r br args ->
    (* Lower a call to another `#lang-pipit` binding `f a1 .. an`. The
       callee's `f_core` has type `exp t [t_n; ...; t_1] r` (innermost-
       first context). We splice arguments in by building an `XLet`
       chain on top of a weakened `f_core` and lowering each argument
       in an env extended with stream binders for the preceding args, so
       caller-side variables get their de Bruijn indices shifted by the
       correct amount. *)
    let arg_tys = br.Ast.br_arg_tys in
    let n_src = L.length arg_tys in
    let n_arg = L.length args in
    if n_src <> n_arg then
      T.fail ("Pipit.Source.Ast.Lower: ACallStream arg count mismatch for "
              ^ R.implode_qn br.Ast.br_fqn ^ ": signature has "
              ^ string_of_int n_src ^ " explicit params, call has "
              ^ string_of_int n_arg ^ " args")
    else
    let core_fqn = core_fqn_of br.Ast.br_fqn in
    let core_fv_tm = T.pack (T.Tv_FVar (T.pack_fv core_fqn)) in
    (* Caller-side stream context (innermost first). *)
    let caller_stream_ctx = stream_ctx_of_binders env.binders in
    (* Callee context (innermost first) = reverse of source param tys. *)
    let callee_ctx = L.rev arg_tys in
    let callee_ctx_tm = context_term env callee_ctx in
    let caller_ctx_tm = context_term env caller_stream_ctx in
    (* The weakened core sits at the bottom of the XLet chain, in
       context `callee_ctx ++ caller_stream_ctx`. *)
    let weakened = `(PXB.weaken #PPS.table #(`#callee_ctx_tm) (`#caller_ctx_tm) (`#core_fv_tm)) in
    (* Lower each argument in env extended with dummy stream binders
       for preceding args (innermost first). *)
    let rec lower_args (acc_dummies_innermost_first: list binder)
                       (defs_innermost_first: list (Ast.sty & T.term))
                       (rem_tys: list Ast.sty)
                       (rem_args: list Ast.ast)
                       : T.Tac (list (Ast.sty & T.term)) =
      match rem_tys, rem_args with
      | [], [] -> defs_innermost_first
      | sty :: rest_tys, a :: rest_args ->
        let cur_env: lower_env = { env with binders = L.append acc_dummies_innermost_first env.binders } in
        let a_tm = lower_stream cur_env a in
        let dummy_name = "__arg_dummy_" ^ string_of_int (T.fresh ()) in
        let dummy: binder = { b_name = dummy_name; b_sty = sty; b_kind = BStream } in
        lower_args (dummy :: acc_dummies_innermost_first)
                   ((sty, a_tm) :: defs_innermost_first)
                   rest_tys rest_args
      | _, _ ->
        T.fail "Pipit.Source.Ast.Lower: ACallStream arg count mismatch (impossible)"
    in
    let defs_innermost_first = lower_args [] [] arg_tys args in
    wrap_xlets env defs_innermost_first weakened

  | Ast.AFby _r lit e ->
    let e_tm = lower_stream env e in
    exp_XFby lit.Ast.lit_tm e_tm

  | Ast.ALet _r n m sty def body ->
    (match m with
     | PPI.Stream ->
       let def_tm = lower_stream env def in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStream } in
       let env' = env_push b env in
       let body_tm = lower_stream env' body in
       exp_XLet (shallow_ty_for_env env sty) def_tm body_tm
     | PPI.Static ->
       (* Encoded as `(fun (n: sty) -> body) def` so that F* substitutes
          `def` for `n` during normalisation. *)
       let def_tm = lower_static env def in
       let nv = fresh_nv n sty in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStatic nv } in
       let env' = env_push b env in
       let body_tm = lower_stream env' body in
       let abs_tm = T.pack (T.Tv_Abs (T.namedv_to_binder nv sty) body_tm) in
       T.mk_app abs_tm [(def_tm, T.Q_Explicit)]
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: ALet with functional mode is not supported: " ^ n))

  | Ast.AMu _r n sty body ->
    let b: binder = { b_name = n; b_sty = sty; b_kind = BStream } in
    let env' = env_push b env in
    let body_tm = lower_stream env' body in
    exp_XMu body_tm

  | Ast.ALetrec _r bs cont ->
    (* v0: support a single static recursive binding only. The legacy
       `Pipit.Plugin.Lift` already treats every `Tv_Let true` as static
       and doesn't recurse into its body, so this is no less expressive.
       Stream-typed recursion belongs to `AMu`; mutual recursion would
       need a tuple encoding and is deferred. *)
    (match bs with
     | [(n, sty, def_ast)] ->
       let nv = fresh_nv n sty in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStatic nv } in
       let env' = env_push b env in
       let def_tm  = lower_static env' def_ast in
       let body_tm = lower_stream env' cont in
       T.pack (T.Tv_Let true [] (T.namedv_to_binder nv sty) def_tm body_tm)
     | [] ->
       T.fail "Pipit.Source.Ast.Lower: ALetrec with no bindings"
     | _ ->
       T.fail "Pipit.Source.Ast.Lower: ALetrec with mutual bindings is not yet supported (only single-binding rec is implemented)")

  | Ast.ACheck _r _olab e ->
    let e_tm = lower_stream env e in
    exp_XCheck e_tm

and lower_static env a =
  match a with
  | Ast.ALit _r lit -> lit.Ast.lit_tm

  | Ast.AVar _r n m ->
    (match m with
     | PPI.Static ->
       (match env_lookup n env.binders with
        | Some b ->
          (match b.b_kind with
           | BStatic nv -> T.pack (T.Tv_Var nv)
           | BStream ->
             T.fail ("Pipit.Source.Ast.Lower: stream variable used in static context: " ^ n))
        | None ->
          T.fail ("Pipit.Source.Ast.Lower: static variable not in scope: " ^ n))
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: non-static variable used in static context: " ^ n))

  | Ast.APrim _r am p args ->
    (match am with
     | Ast.AppPureConst ->
       (* Direct F* application. *)
       let arg_tms = T.map (fun a -> (lower_static env a, T.Q_Explicit)) args in
       T.mk_app p.Ast.prim_fn arg_tms
     | _ ->
       T.fail "Pipit.Source.Ast.Lower: APrim with stream app_mode used in static context")

  | Ast.ACallStream _r _br _args ->
    T.fail "Pipit.Source.Ast.Lower: ACallStream used in static context (stream-aware calls only valid in stream context)"

  | _ ->
    T.fail "Pipit.Source.Ast.Lower: static lowering only supports ALit, AVar, and APrim AppPureConst so far"

(* Top-level entry: lower an AST node as a stream/exp term. *)
let lower (env: lower_env) (a: Ast.ast): T.Tac T.term =
  lower_stream env a
