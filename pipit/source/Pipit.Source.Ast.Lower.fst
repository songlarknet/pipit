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
module TermEq = FStar.Reflection.TermEq.Simple

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface
module PPS = Pipit.Prim.Shallow
module PPT = Pipit.Prim.Table
module PXB = Pipit.Exp.Base
module PM  = Pipit.Prop.Metadata
module PSSB = Pipit.Prim.HasStream
module PTB = Pipit.Tactics.Base
module PSAU = Pipit.Source.Ast.Util

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
   to the quasi-quote `PSSB.shallow sty` form (works for ground types).

   `prim_acc` is the per-sigelt prim hoist cache: each entry pairs a
   record term `Mkprim id ft fn` with the `Tv_FVar` reference to the
   top-level `unfold let __xprim_<N>` sigelt the lifter will emit for
   it (see `flush_prim_acc`). Hoisting prevents F* from re-elaborating
   the same `mkPrim ... ft ... fn` record at every `XPrim` site, which
   was the cost driver behind the V2b lifter explosion (manual
   reproduction: `Plugin.Test.Bug.MasterModes.V2b.Literal.fst`). The
   hoisted helpers are marked `unfold` so `__xprim_<N>.prim_ty`
   reduces to the constructor projection `ft` during XApp unification.

   `prim_module` is the FQN prefix used to name the generated helpers
   — typically the current splice module followed by a unique
   per-binding tag. *)
noeq
type lower_env = {
  binders: list binder;
  inst_for: T.term -> T.Tac (option T.term);
  (* The current cexp context as an F* term of type
     `PPT.context PPS.table`. Every cexp constructor wrapper
     (`xprm`/`xval`/`xbvar`/`xapp`/`xapps`/`xlet`/`xmu`/`xfby`/`xcheck`)
     takes the context EXPLICITLY (not implicitly), and the emitters
     pass this term verbatim. Each time a stream binder is pushed
     onto the cexp context, `extend_ctx` hoists a fresh top-level
     `let __ctx_<N> : PPT.context PPS.table = sty :: __ctx_<prev>`
     helper sigelt (drained by `flush_ctx_acc`) and repoints `ctx_tm`
     to an `FVar __ctx_<N>` so all interior sites in the body share
     that name. This eliminates per-site `?c` unification metavariables
     that drove the V2a/V2b explosion AND keeps each emitted cexp
     term tiny (one fvar) instead of inlining the entire cons chain.

     The initial term (set by `Pipit.Plugin.Lift` before calling
     `lower`) is an `FVar __ctx_<tag>_init` pointing at a hoisted
     `let __ctx_<tag>_init = [shallow t1; ...; shallow tn]` for the
     top-level stream params (also recorded in `ctx_acc`). *)
  ctx_tm: T.term;
  prim_acc: T.tref (list (T.term & T.term));
  (* Per-sigelt cache of hoisted ctx helpers. Each entry is
     `(def_tm, fv_tm)` where `def_tm` is the full body
     (`sty :: <prev_ctx_fv>` or the initial literal list) and
     `fv_tm` is the `FVar __ctx_<tag>_<N>` reference. Drained by
     `flush_ctx_acc` after lowering. Each emitted ctx helper is
     wrapped in `Tv_Abs` over `ctx_passthrough` so that polymorphic
     source bindings (with `#a:eqtype {| has_stream a |}` params)
     can reference the same type/instance binders in their ctx
     definitions; at use sites, `intern_ctx` returns the FVar
     APPLIED to those passthrough binders' namedvs. *)
  ctx_acc: T.tref (list (T.term & T.term));
  (* The polymorphic / typeclass passthrough binders of the source
     binding being lowered. Empty for monomorphic bindings (Smoke
     tests, ground-typed examples). For polymorphic bindings (e.g.
     `let poly_id (#a: eqtype) {| has_stream a |} ...`) these are
     the binders that wrap the main core sigelt's `lb_def` /
     `lb_typ`; we wrap every hoisted `__ctx_<N>` helper in the same
     binders so its `def_tm` (which may reference `a` and the
     instance) is well-scoped at top level. *)
  ctx_passthrough: list T.binder;
  prim_module: list string;
  prim_tag: string;
}

(* `empty_env ()` allocates a fresh prim cache and uses an unscoped
   "__xprim_empty_" prefix. Callers in `Pipit.Plugin.Lift` should
   instead build a `lower_env` directly with the splice's module path
   and binding name, so generated helper names don't collide across
   bindings. *)
let empty_env (): T.Tac lower_env = {
  binders = [];
  inst_for = (fun _ -> None);
  ctx_tm = `([] <: Pipit.Prim.Table.context Pipit.Prim.Shallow.table);
  prim_acc = T.alloc [];
  ctx_acc = T.alloc [];
  ctx_passthrough = [];
  prim_module = [];
  prim_tag = "empty";
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

(* Splice-friendly wrappers used by the lifter to pin the result-type
   structure at each cexp construction site. They take the cexp
   context `c` EXPLICITLY (not as an implicit), so when the lifter
   passes a concrete top-level `__ctx_<N>` Tv_Var at every site, F*
   never has to unify per-site `?c` metavariables against each other
   through the surrounding XApp/XApps/XLet/XMu skeleton. Without this
   (or with a wrapper-less raw-constructor encoding) the lifter's
   nested cexps trigger an exponential unification blow-up on deeply
   nested cexps (V2a/V2b master-modes reproduction).

   They are `unfold` so the rest of the pipeline (semantics, weakening,
   CSE, extraction, checked-blessing) sees the canonical bare-constructor
   form when pattern-matching. *)

unfold
let xprm (c: PPT.context PPS.table) (p: PPS.prim): PXB.exp_apps PPS.table c p.prim_ty =
  PXB.XPrim p

unfold
let xval (c: PPT.context PPS.table) (#valty: PPS.shallow_type) (v: valty.PPS.ty_sem)
  : PXB.exp PPS.table c valty
  = PXB.XBase (PXB.XVal v)

unfold
let xbvar (c: PPT.context PPS.table) (i: Pipit.Context.Base.index_lookup c)
  : PXB.exp PPS.table c (Pipit.Context.Base.get_index c i)
  = PXB.XBase (PXB.XBVar i)

unfold
let xapp (c: PPT.context PPS.table) (#arg: PPS.shallow_type) (#ret: PPT.funty PPS.shallow_type)
         (f: PXB.exp_apps PPS.table c (PPT.FTFun arg ret)) (e: PXB.exp PPS.table c arg)
  : PXB.exp_apps PPS.table c ret
  = PXB.XApp f e

unfold
let xapps (c: PPT.context PPS.table) (#valty: PPS.shallow_type)
          (e: PXB.exp_apps PPS.table c (PPT.FTVal valty))
  : PXB.exp PPS.table c valty
  = PXB.XApps e

unfold
let xlet (c: PPT.context PPS.table) (#valty: PPS.shallow_type) (b: PPS.shallow_type)
         (def: PXB.exp PPS.table c b) (body: PXB.exp PPS.table (b :: c) valty)
  : PXB.exp PPS.table c valty
  = PXB.XLet b def body

unfold
let xmu (c: PPT.context PPS.table) (#valty: PPS.shallow_type)
        (body: PXB.exp PPS.table (valty :: c) valty)
  : PXB.exp PPS.table c valty
  = PXB.XMu body

unfold
let xfby (c: PPT.context PPS.table) (#valty: PPS.shallow_type)
         (v: valty.PPS.ty_sem) (e: PXB.exp PPS.table c valty)
  : PXB.exp PPS.table c valty
  = PXB.XFby v e

unfold
let xcheck (c: PPT.context PPS.table) (ps: PM.prop_status)
           (e: PXB.exp PPS.table c PPS.table.propty)
  : PXB.exp PPS.table c PPS.table.unitty
  = PXB.XCheck ps e

let exp_XVal  (env: lower_env) (v: T.term): T.term =
  `(xval (`#env.ctx_tm) (`#v))

let exp_XBVar (env: lower_env) (i: T.term): T.term =
  `(xbvar (`#env.ctx_tm) (`#i))

let exp_XLet  (env: lower_env) (sty: T.term) (def: T.term) (body: T.term): T.term =
  `(xlet (`#env.ctx_tm) (`#sty) (`#def) (`#body))

let exp_XMu   (env: lower_env) (body: T.term): T.term =
  `(xmu (`#env.ctx_tm) (`#body))

let exp_XFby  (env: lower_env) (v: T.term) (e: T.term): T.term =
  `(xfby (`#env.ctx_tm) (`#v) (`#e))

let exp_XCheck (env: lower_env) (e: T.term): T.term =
  `(xcheck (`#env.ctx_tm) PM.PSUnknown (`#e))

(* Compute the FQN of a lifted source binding's core sigelt via the
   `[@@core_of_source]` attribute. Hand-written wrappers (no
   `[@@core_lifted]`) win over the auto-generated `<nm>_core` splice
   when both carry `[@@core_of_source src]`, so a user can override
   the raw lift with e.g. a contract-wrapped `body_contract`.

   See `Pipit.Source.Ast.Util.find_core_for_source` for the lookup
   policy. *)
let core_fqn_of (src: Ast.fqn): T.Tac Ast.fqn =
  let tac_env = T.top_env () in
  PSAU.find_core_for_source tac_env (R.implode_qn src)

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

(* Push a fresh stream binder of shallow type `sh_sty_tm` onto the
   cexp context. Returns a tuple `(env', wrap)` where:
     - `env'.ctx_tm = sh_sty_tm :: env.ctx_tm` is a fresh literal cons
       cell whose tail is the running ctx_tm;
     - `wrap body = body` is a no-op (kept as a tuple slot in case we
       reintroduce per-binder `let __ctx_<N>` sharing later — see
       commit history for the failed attempt: F* leaves
       `get_index __ctx_<N> i` stuck through `Tv_Let` bindings).

   We hoist each cexp context to a TOP-LEVEL `let __ctx_<tag>_<N>
   : PPT.context PPS.table = sty :: __ctx_<tag>_<N-1>` sigelt
   (drained by `flush_ctx_acc`). Top-level lets DO get unfolded by
   F* during type-level reduction (unlike `Tv_Let` locals), so
   `get_index __ctx_<N> i` reduces normally. This shares the cons
   chain across every emit site in the body (no per-site cons
   literal duplication) AND keeps the surrounding wrappers' explicit
   `c: PPT.context PPS.table` reasoning fast. The combination of
   explicit-c wrappers + named ctx hoisting is what restores the
   manual-reproduction performance (~1.4s for V2b) compared to
   inlined cons chains at every site (>120s for V2b post-Tv_Let). *)
(* Normalize a binder qualifier for use as an application argument
   qualifier. `Q_Meta` in a binder position means "if the caller
   doesn't supply this arg, run this tactic"; at the call site we
   ARE supplying the arg, so treat it as `Q_Implicit`. *)
let norm_passthrough_q (q: T.aqualv): T.aqualv =
  match q with
  | T.Q_Meta _ -> T.Q_Implicit
  | _ -> q

(* Apply a head term to each passthrough binder as a `Tv_Var` arg
   carrying the binder's (normalized) qualifier. Used by `intern_ctx`
   so callers receive a `__ctx_N #a {| s_a |}` term ready to drop
   into `env.ctx_tm`. *)
let apply_passthrough (head: T.term) (bs: list T.binder): T.term =
  L.fold_left
    (fun (acc: T.term) (b: T.binder) ->
      let nv_tm: T.term = T.pack (T.Tv_Var (T.binder_to_namedv b)) in
      let q = norm_passthrough_q b.qual in
      T.pack (T.Tv_App acc (nv_tm, q)))
    head bs

let intern_ctx (env: lower_env) (def_tm: T.term): T.Tac T.term =
  let entries = T.read env.ctx_acc in
  let n = T.fresh () in
  let nm = L.append env.prim_module
    ["__ctx_" ^ env.prim_tag ^ "_" ^ string_of_int n] in
  let fv_tm = T.pack (T.Tv_FVar (T.pack_fv nm)) in
  T.write env.ctx_acc ((def_tm, fv_tm) :: entries);
  apply_passthrough fv_tm env.ctx_passthrough

let extend_ctx (env: lower_env) (sh_sty_tm: T.term): T.Tac (lower_env & (T.term -> T.Tac T.term)) =
  let def_tm: T.term = `((`#sh_sty_tm) :: (`#env.ctx_tm)) in
  let fv_tm = intern_ctx env def_tm in
  let wrap (body: T.term): T.Tac T.term = body in
  ({ env with ctx_tm = fv_tm }, wrap)

(* Wrap a body with a chain of XLets. The three lists are in lockstep
   in innermost-first order (i.e. element 0 corresponds to the
   innermost XLet, closest to `body`):
     - `envs_innermost_first[k]`: the lower_env whose `ctx_tm` matches
       the OUTER ctx of the k-th XLet (i.e. the env BEFORE that XLet's
       binder is pushed).
     - `defs_innermost_first[k] = (sty_k, def_k)`: the source type and
       lowered def of the k-th XLet's binding.
     - `wraps_innermost_first[k]`: the `__ctx_<N>` extend_ctx wrap to
       apply to the k-th XLet's BODY (so all nested XLets and their
       defs share the named cexp context for that binder level).
   The innermost iteration's wrap is applied around `body` itself,
   which is harmless even if `body` doesn't reference the freshly
   introduced `__ctx_<N>`. *)
let rec wrap_xlets (envs_innermost_first: list lower_env)
                   (defs_innermost_first: list (Ast.sty & T.term))
                   (wraps_innermost_first: list (T.term -> T.Tac T.term))
                   (body: T.term): T.Tac T.term =
  match envs_innermost_first, defs_innermost_first, wraps_innermost_first with
  | [], [], [] -> body
  | env_here :: envs_rest, (sty, def) :: defs_rest, (wrap_here: T.term -> T.Tac T.term) :: wraps_rest ->
    let sh = shallow_ty_for_env env_here sty in
    let wrapped_body = wrap_here body in
    let inner = exp_XLet env_here sh def wrapped_body in
    wrap_xlets envs_rest defs_rest wraps_rest inner
  | _, _, _ ->
    T.fail "Pipit.Source.Ast.Lower: wrap_xlets envs/defs/wraps length mismatch (impossible)"

(* Build a `funty shallow_type` term from argument and return source
   types: `FTFun a1 (FTFun a2 ... (FTVal r)) ...`. *)
let rec funty_of (env: lower_env) (arg_tys: list Ast.sty) (ret_ty: Ast.sty): T.Tac T.term =
  match arg_tys with
  | [] -> let r = shallow_ty_for_env env ret_ty in `(PPT.FTVal (`#r))
  | a :: rest ->
    let tail = funty_of env rest ret_ty in
    let sh = shallow_ty_for_env env a in
    `(PPT.FTFun (`#sh) (`#tail))

(* Build a `PPS.prim` record term `Pipit.Prim.Shallow.Mkprim id ft fn`
   (the raw constructor application, NOT the `mkPrim` helper — which
   is a regular `let` whose body does not reduce during F* unification).
   Using the constructor directly means a hoisted `unfold let
   __xprim_<N> : PPS.prim = Mkprim id ft fn` exposes
   `__xprim_<N>.prim_ty` as the direct projection `ft` after one
   reduction step, which is what every `XApp`'s implicit `arg`/`ret`
   inference needs. The `id` is wrapped as `Some s` / `None`. *)
let prim_record_tm (id_tm ft_tm fn_tm: T.term): T.term =
  let ctor: T.term =
    T.pack (T.Tv_FVar (T.pack_fv ["Pipit"; "Prim"; "Shallow"; "Mkprim"])) in
  PTB.mk_apps_explicit ctor [id_tm; ft_tm; fn_tm]

(* Build (or look up) the FVar reference for a prim record. The first
   time a syntactically-distinct prim record is requested in this
   sigelt, allocate a fresh name `<prim_module>.__xprim_<prim_tag>_<N>`
   and push the record onto `env.prim_acc`. Subsequent calls with a
   structurally-equal record return the same FVar so the cexp body
   shares one helper per unique prim. The lifter (`Pipit.Plugin.Lift`)
   reads `prim_acc` after lowering and emits the helper sigelts via
   `flush_prim_acc` BEFORE the main core sigelt. *)
let rec find_prim_in_acc (record_tm: T.term) (xs: list (T.term & T.term)): Tot (option T.term) =
  match xs with
  | [] -> None
  | (rec_tm, fv_tm) :: rest ->
    if TermEq.term_eq rec_tm record_tm then Some fv_tm
    else find_prim_in_acc record_tm rest

let intern_prim (env: lower_env) (record_tm: T.term): T.Tac T.term =
  let entries = T.read env.prim_acc in
  match find_prim_in_acc record_tm entries with
  | Some fv_tm -> apply_passthrough fv_tm env.ctx_passthrough
  | None ->
    let n = T.fresh () in
    let nm = L.append env.prim_module
      ["__xprim_" ^ env.prim_tag ^ "_" ^ string_of_int n] in
    let fv_tm = T.pack (T.Tv_FVar (T.pack_fv nm)) in
    T.write env.prim_acc ((record_tm, fv_tm) :: entries);
    apply_passthrough fv_tm env.ctx_passthrough

(* Build a hoisted `PPS.prim` reference: builds the record term, then
   memoises through `env.prim_acc` and returns an `FVar` to the
   to-be-emitted top-level helper sigelt. *)
let shallow_prim (env: lower_env) (id: option Ast.name) (arg_tys: list Ast.sty) (ret_ty: Ast.sty) (fn: T.term): T.Tac T.term =
  let id_tm: T.term =
    match id with
    | Some s -> `(Some (`#(T.pack (T.Tv_Const (T.C_String s)))))
    | None   -> `None
  in
  let ft_tm = funty_of env arg_tys ret_ty in
  let record_tm = prim_record_tm id_tm ft_tm fn in
  intern_prim env record_tm

(* Drain `env.prim_acc` and emit one plain top-level `let <name>
   : PPS.prim = <record>` sigelt per cached prim. Each is tagged
   with the `core_lifted_prim` attribute so the discharge tactic's
   `Pipit.Tactics.norm_full` delta-unfolds it on demand. We do NOT
   set `Unfold_for_unification_and_vcgen`: doing so would force F*
   to eagerly delta the helper into every use site during the splice
   re-typecheck, which is expensive once the lifter emits many of
   these per cexp. Leaving them opaque to the unifier costs nothing
   because the only consumer that needs `(record).prim_ty` reduced
   is the SMT-side discharge tactic, which has its own delta_attr
   list. *)
let flush_prim_acc (env: lower_env): T.Tac (list T.sigelt) =
  let entries = T.read env.prim_acc in
  let prim_ty_tm: T.term =
    T.pack (T.Tv_FVar (T.pack_fv ["Pipit"; "Prim"; "Shallow"; "prim"])) in
  let lb_typ_wrapped: T.term =
    L.fold_right
      (fun (b: T.binder) (acc: T.term) -> T.pack (T.Tv_Arrow b (T.C_Total acc)))
      env.ctx_passthrough
      prim_ty_tm in
  let attrs: list T.term = [ `Pipit.Plugin.Interface.core_lifted_prim ] in
  let mk_sigelt (entry: T.term & T.term): T.Tac T.sigelt =
    let (record_tm, fv_tm) = entry in
    let def_wrapped: T.term =
      L.fold_right
        (fun (b: T.binder) (acc: T.term) -> T.pack (T.Tv_Abs b acc))
        env.ctx_passthrough
        record_tm in
    let nm: R.name = match T.inspect fv_tm with
      | T.Tv_FVar fv -> T.inspect_fv fv
      | _ -> [] in
    let lb: T.letbinding = {
      lb_fv  = T.pack_fv nm;
      lb_us  = [];
      lb_typ = lb_typ_wrapped;
      lb_def = def_wrapped;
    } in
    let se: T.sigelt = T.pack_sigelt (T.Sg_Let { isrec = false; lbs = [lb] }) in
    (* Intentionally no `Unfold_for_unification_and_vcgen` qual — see
       comment on `flush_prim_acc` above. *)
    let se = R.set_sigelt_attrs attrs se in
    (if T.ext_getv "pipit:lift:debug" <> ""
     then T.print ("hoisted prim helper: " ^ R.implode_qn nm ^ " := " ^ T.term_to_string def_wrapped)
     else ());
    se
  in
  L.rev (T.map mk_sigelt entries)

(* Drain `env.ctx_acc` and emit one plain top-level `let __ctx_<N>
   : PPT.context PPS.table = <def>` sigelt per cached ctx. Entries
   are accumulated newest-first (`extend_ctx` prepends), so we
   `L.rev` to emit oldest-first — this is dependency order since
   each `__ctx_<N>` references `__ctx_<N-1>` in its def. Each helper
   is tagged with the `core_lifted_ctx` attribute so the discharge
   tactic's `Pipit.Tactics.norm_full` delta-unfolds it on demand.
   We deliberately do NOT set `Unfold_for_unification_and_vcgen`:
   that would expand the full Cons spine into every typing site of
   the cexp body (each `XBVar n` typed at `index __ctx_k n`),
   ballooning the splice re-typecheck cost (V2b: 6.4s -> 24.0s for
   ctx-unfold alone). The SMT discharge tactic (which actually needs
   the concrete list to chain `length`/`index`) gets it via the
   delta_attr path instead. *)
let flush_ctx_acc (env: lower_env): T.Tac (list T.sigelt) =
  let entries = T.read env.ctx_acc in
  let ctx_ty_tm: T.term =
    `(Pipit.Prim.Table.context Pipit.Prim.Shallow.table) in
  (* Wrap lb_typ in `Tv_Arrow` over passthrough binders so the
     emitted helper's type is `(#a:eqtype) -> ... -> PPT.context
     PPS.table` for polymorphic source bindings (and just `PPT.context
     PPS.table` when passthrough is empty). *)
  let lb_typ_wrapped: T.term =
    L.fold_right
      (fun (b: T.binder) (acc: T.term) -> T.pack (T.Tv_Arrow b (T.C_Total acc)))
      env.ctx_passthrough
      ctx_ty_tm in
  let mk_sigelt (entry: T.term & T.term): T.Tac T.sigelt =
    let (def_tm, fv_tm) = entry in
    (* Wrap lb_def in `Tv_Abs` over the same passthrough binders so
       free namedv occurrences in `def_tm` (from `shallow_ty_with_inst`
       calls and from prior `__ctx_<N-1>` applications) get bound. *)
    let def_wrapped: T.term =
      L.fold_right
        (fun (b: T.binder) (acc: T.term) -> T.pack (T.Tv_Abs b acc))
        env.ctx_passthrough
        def_tm in
    let nm: R.name = match T.inspect fv_tm with
      | T.Tv_FVar fv -> T.inspect_fv fv
      | _ -> [] in
    let lb: T.letbinding = {
      lb_fv  = T.pack_fv nm;
      lb_us  = [];
      lb_typ = lb_typ_wrapped;
      lb_def = def_wrapped;
    } in
    let se: T.sigelt = T.pack_sigelt (T.Sg_Let { isrec = false; lbs = [lb] }) in
    (* Intentionally no `Unfold_for_unification_and_vcgen` qual — see
       comment on `flush_ctx_acc` above. *)
    let se = R.set_sigelt_attrs [ `Pipit.Plugin.Interface.core_lifted_ctx ] se in
    (if T.ext_getv "pipit:lift:debug" <> ""
     then T.print ("hoisted ctx helper: " ^ R.implode_qn nm ^ " := " ^ T.term_to_string def_wrapped)
     else ());
    se
  in
  L.rev (T.map mk_sigelt entries)

let exp_XPrim (env: lower_env) (p_tm: T.term): T.term =
  `(xprm (`#env.ctx_tm) (`#p_tm))

let exp_XApp  (env: lower_env) (f: T.term) (a: T.term): T.term =
  `(xapp (`#env.ctx_tm) (`#f) (`#a))

let exp_XApps (env: lower_env) (e: T.term): T.term =
  `(xapps (`#env.ctx_tm) (`#e))

let int_const (i: int): T.term =
  T.pack (T.Tv_Const (T.C_Int i))

(* Allocate a fresh named variable of the given F* type and pretty name. *)
let fresh_nv (ppname: string) (ty: T.term): T.Tac T.namedv =
  { uniq = T.fresh (); sort = T.seal ty; ppname = R.as_ppname ppname }

(*** ALetMatch desugaring helpers ***)

(* Walk an [Ast.pat] (built by [Pipit.Source.Ast.Reflect.pat_of_fstar])
   and turn it into a chain of stream [Ast.ALet]s wrapping [body].
   Each leaf [PVar] becomes one [ALet] whose RHS is the appropriate
   projector application on [parent_nm]; nested [PCon] sub-patterns
   introduce an intermediate `_dst#N` name and recurse. [PWild]
   contributes no binding.

   Projector typechecking uses [T.top_env ()]; this is sufficient for
   destructure whose scrutinee type is ground at the splice site
   (tuples / records over concrete types — every test we have today).
   Polymorphic destructure (e.g. a `match` on `stream (a * b)` inside a
   `#a:eqtype -> #b:eqtype -> ...` source binding) would need the
   local type binders in scope; that would require threading a tactic
   env through [lower_env]. Deferred. *)

let rec pat_size (p: Ast.pat): nat =
  match p with
  | Ast.PCon _ subs -> 1 + pats_size subs
  | _ -> 1

and pats_size (ps: list Ast.pat): nat =
  match ps with
  | [] -> 0
  | p :: rest -> 1 + pat_size p + pats_size rest

(* Pattern/constructor helpers are shared with [Reflect] -- see
   [Pipit.Source.Ast.Util]. *)
let projector_fqn: Ast.fqn -> Ast.name -> T.Tac Ast.fqn = PSAU.projector_fqn
let ctor_field_names: T.env -> T.fv -> T.Tac (list Ast.name) = PSAU.ctor_field_names
let scrut_type_implicits: T.term -> T.Tac (list T.argv) = PSAU.scrut_type_implicits

(* Build an [Ast.prim] for a projector pre-applied to scrutinee type
   implicits. Mirrors [Pipit.Source.Ast.Reflect.of_prim_fv_applied]. *)
let mk_proj_prim (env: T.env) (proj_fqn: Ast.fqn) (implicits: list T.argv): T.Tac Ast.prim =
  let proj_fv = T.pack_fv proj_fqn in
  let proj_tm = T.pack (T.Tv_FVar proj_fv) in
  let proj_fn =
    match implicits with
    | [] -> proj_tm
    | _  -> T.mk_app proj_tm implicits
  in
  let ty        = T.tc env proj_fn in
  let (args, c) = T.collect_arr ty in
  let res_ty    = PTB.returns_of_comp c in
  {
    Ast.prim_id      = Some (R.implode_qn proj_fqn);
    Ast.prim_arg_tys = args;
    Ast.prim_ret_ty  = res_ty;
    Ast.prim_fn      = proj_fn;
  }

(* Desugar an [Ast.pat] against a parent named-binder [parent_nm] of
   type [parent_sty], producing an [Ast.ast] equivalent to the
   irrefutable destructure wrapped around [body]. *)
let rec pat_to_alet_chain (rng: R.range) (pat: Ast.pat)
                          (parent_nm: Ast.name) (parent_sty: Ast.sty)
                          (body: Ast.ast)
    : T.Tac Ast.ast
      (decreases (pat_size pat))
=
  match pat with
  | Ast.PWild -> body

  | Ast.PVar nm field_sty mode ->
    (* The whole parent value is bound to nm. *)
    let def = Ast.AVar rng parent_nm mode in
    Ast.ALet rng nm mode field_sty def body

  | Ast.PCon ctor_fqn sub_pats ->
    let env = T.top_env () in
    let ctor_fv = T.pack_fv ctor_fqn in
    let field_names = ctor_field_names env ctor_fv in
    (if L.length field_names <> L.length sub_pats then
      T.fail "Pipit.Source.Ast.Lower: pat arity mismatch (sub_pats vs ctor fields)"
     else ());
    let implicits = scrut_type_implicits parent_sty in
    pat_to_alet_chain_subs rng ctor_fqn field_names sub_pats implicits parent_nm body

and pat_to_alet_chain_subs (rng: R.range) (ctor_fqn: Ast.fqn)
                           (fields: list Ast.name) (subs: list Ast.pat)
                           (implicits: list T.argv) (parent_nm: Ast.name)
                           (body: Ast.ast)
    : T.Tac Ast.ast
      (decreases (pats_size subs))
=
  match fields, subs with
  | [], [] -> body
  | f :: fs, p :: ps ->
    (* Build the let chain for the remaining fields first; this field's
       binding is then placed OUTSIDE that, matching the source order. *)
    let rest = pat_to_alet_chain_subs rng ctor_fqn fs ps implicits parent_nm body in
    (match p with
     | Ast.PWild -> rest
     | Ast.PVar nm field_sty mode ->
       let env = T.top_env () in
       let proj_fqn = projector_fqn ctor_fqn f in
       let proj_prim = mk_proj_prim env proj_fqn implicits in
       let parent_ref = Ast.AVar rng parent_nm PPI.Stream in
       let proj_def: Ast.ast = Ast.APrim rng Ast.AppPureStream proj_prim [parent_ref] in
       Ast.ALet rng nm mode field_sty proj_def rest
     | Ast.PCon _ _ ->
       (* Nested constructor: bind an intermediate name to the projector
          application, then recurse on the nested pat. *)
       let env = T.top_env () in
       let proj_fqn = projector_fqn ctor_fqn f in
       let proj_prim = mk_proj_prim env proj_fqn implicits in
       let mid_nm = "_dst#" ^ string_of_int (T.fresh ()) in
       let mid_ty = proj_prim.Ast.prim_ret_ty in
       let parent_ref = Ast.AVar rng parent_nm PPI.Stream in
       let proj_def: Ast.ast = Ast.APrim rng Ast.AppPureStream proj_prim [parent_ref] in
       let nested = pat_to_alet_chain rng p mid_nm mid_ty rest in
       Ast.ALet rng mid_nm PPI.Stream mid_ty proj_def nested)
  | _, _ ->
    T.fail "Pipit.Source.Ast.Lower: pat sub arity mismatch (impossible)"

(*** AMatch (static multi-arm) desugaring helpers ***)

(* Termination measures for walking a [T.pattern] when pushing static
   binders for the arms of an [AMatch AppPureConst]. Parallel to the
   measures in [Pipit.Source.Ast.Reflect] but separately named so they
   don't shadow the [pat_size] on [Ast.pat] above. *)
let rec tpat_size (p: T.pattern): nat =
  match p with
  | T.Pat_Cons pc -> 1 + tpat_bool_subpats_size pc.subpats
  | _ -> 1

and tpat_bool_subpats_size (ss: list (T.pattern & bool)): nat =
  match ss with
  | [] -> 0
  | (p, _) :: rest -> 1 + tpat_size p + tpat_bool_subpats_size rest

(* Walk a [T.pattern] and push each leaf [Pat_Var] as a STATIC binder
   into [env], in pattern walk order (explicit subpats only). The
   pushed namedv is the pattern variable's original [bv.v] (preserving
   the uniq), and the binder name is computed using Reflect's
   convention ([ppname ^ "#" ^ string_of_int uniq]) so that the lifted
   body's name-based [AVar] lookups resolve to the namedv we just
   pushed. The arm's [T.pattern] can then be re-emitted verbatim
   under [Tv_Match] and F* will bind the pattern's bvs to occurrences
   of the same namedv in the lowered body. *)
let rec push_static_pat_binders (pat: T.pattern) (env: lower_env)
    : T.Tac lower_env
      (decreases (tpat_size pat))
=
  match pat with
  | T.Pat_Var pv ->
    let nv: T.namedv = pv.v in
    let nm: Ast.name = PSAU.mk_uniq_ast_name nv in
    let sty: Ast.sty = T.unseal pv.sort in
    let b: binder = { b_name = nm; b_sty = sty; b_kind = BStatic nv } in
    env_push b env

  | T.Pat_Cons pc ->
    push_static_pat_binders_subs pc.subpats env

  | _ ->
    env

and push_static_pat_binders_subs (ss: list (T.pattern & bool)) (env: lower_env)
    : T.Tac lower_env
      (decreases (tpat_bool_subpats_size ss))
=
  match ss with
  | [] -> env
  | (_, true)  :: rest ->
    (* Implicit subpats — these correspond to elided type/dot
       arguments and don't introduce binders; skip them, matching the
       walk order used by [pat_of_fstar] in Reflect. *)
    push_static_pat_binders_subs rest env
  | (p, false) :: rest ->
    let env' = push_static_pat_binders p env in
    push_static_pat_binders_subs rest env'

(*** Entry points ***)

val lower_stream (env: lower_env) (a: Ast.ast): T.Tac T.term

val lower_static (env: lower_env) (a: Ast.ast): T.Tac T.term

let rec lower_stream env a =
  match a with
  | Ast.ALit _r lit ->
    exp_XVal env lit.Ast.lit_tm

  | Ast.AVar _r n m ->
    (match m with
     | PPI.Stream ->
       (match env_bvar_index n env.binders with
        | Some i -> exp_XBVar env (int_const i)
        | None -> T.fail ("Pipit.Source.Ast.Lower: stream variable not in scope: " ^ n))
     | PPI.Static ->
       (* Static values are lifted into stream context via XVal. *)
       let v_tm = lower_static env a in
       exp_XVal env v_tm
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: unexpected functional mode on AVar: " ^ n))

  | Ast.APrim _r am p args ->
    (match am with
     | Ast.AppPureStream ->
       (* XApps (XApp (... (XApp (XPrim p) a1) ...) an) *)
       let prim_tm  = shallow_prim env p.Ast.prim_id p.Ast.prim_arg_tys p.Ast.prim_ret_ty p.Ast.prim_fn in
       let head     = exp_XPrim env prim_tm in
       let arg_tms  = T.map (lower_stream env) args in
       let applied  = L.fold_left (exp_XApp env) head arg_tms in
       exp_XApps env applied
     | Ast.AppPureConst ->
       (* Static-only application; lift the resulting value into stream
          context via XVal. *)
       let v_tm = lower_static env a in
       exp_XVal env v_tm)

  | Ast.ACallStream _r br args ->
    (* Lower a call to another `#lang-pipit` binding `f a1 .. an`. The
       callee's `f_core` may be polymorphic over Static F* params
       (real `Tv_Abs` binders) followed by a cexp expression in its
       Stream params: `f_core : s1 -> ... -> sk -> exp t [tn; ...; t1] r`
       (innermost-first context, stream params only). We:
         1. Walk `br.br_mode` to split args into static (lowered to F*
            terms and applied via `Tv_App`) and stream (kept for the
            cexp `XLet`/`weaken` chain).
         2. Build the cexp ctx and weaken/XLet chain from the stream
            args only, in source order. Static args are out of band
            and don't shift caller de Bruijn indices. *)
    let arg_tys = br.Ast.br_arg_tys in
    let n_src = L.length arg_tys in
    let n_arg = L.length args in
    if n_src <> n_arg then
      T.fail ("Pipit.Source.Ast.Lower: ACallStream arg count mismatch for "
              ^ R.implode_qn br.Ast.br_fqn ^ ": signature has "
              ^ string_of_int n_src ^ " explicit params, call has "
              ^ string_of_int n_arg ^ " args")
    else
    (* Split args into (static asts in source order, (stream ast, sty)
       pairs in source order) by peeling one EXPLICIT `ModeFun` layer
       per arg from `br.br_mode`. `br_mode` contains one layer per
       source binder (including implicits / instance binders), so we
       drop leading `ModeFun ... explicit=false ...` layers first.
       Defensive default: treat as Stream if `br_mode` is exhausted. *)
    let rec partition_args (m: PPI.mode) (args: list Ast.ast) (tys: list Ast.sty)
      : T.Tac (list Ast.ast & list (Ast.ast & Ast.sty))
    =
      match args, tys with
      | [], [] -> ([], [])
      | a :: ras, t :: rts ->
        let m = PSAU.skip_implicit_modes m in
        let (arg_mode, rm): PPI.mode & PPI.mode = match m with
          | PPI.ModeFun am _ rm -> (am, rm)
          | _ -> (PPI.Stream, m)
        in
        let (ss, sts) = partition_args rm ras rts in
        (match arg_mode with
         | PPI.Static -> (a :: ss, sts)
         | _ -> (ss, (a, t) :: sts))
      | _, _ ->
        T.fail "Pipit.Source.Ast.Lower: ACallStream arg/ty mismatch (impossible)"
    in
    let (static_args, stream_args_tys) = partition_args br.Ast.br_mode args arg_tys in
    let core_fqn = core_fqn_of br.Ast.br_fqn in
    let core_fv_tm = T.pack (T.Tv_FVar (T.pack_fv core_fqn)) in
    (* Pre-apply the call-site implicits to the callee's `__core_*`
       reference so polymorphic callees become monomorphic at this
       call site. For ground callees `br_implicits` is empty and this
       is a no-op. *)
    let core_fv_tm =
      match br.Ast.br_implicits with
      | [] -> core_fv_tm
      | _  -> T.mk_app core_fv_tm br.Ast.br_implicits
    in
    (* Apply each static arg as an F* `Tv_App` (explicit) to the core
       reference, in source order (outermost-static first). *)
    let core_fv_tm =
      T.fold_left
        (fun (acc: T.term) (a: Ast.ast) ->
          PTB.mk_app_explicit acc (lower_static env a))
        core_fv_tm
        static_args
    in
    let stream_tys = L.map snd stream_args_tys in
    let stream_args = L.map fst stream_args_tys in
    (* Callee context (innermost first) = reverse of stream param tys. *)
    let callee_ctx = L.rev stream_tys in
    let callee_ctx_tm = context_term env callee_ctx in
    (* Use the env's shared `ctx_tm` (a `Tv_Var __ctx_<N>`) as the
       caller-side stream context, not a fresh literal cons chain. The
       surrounding XLets' explicit-`c` wrappers reference exactly this
       Tv_Var, and the per-binder `extend_ctx` chain reduces
       `__ctx_<inner>` down to `t_n :: ... :: t_1 :: env.ctx_tm`,
       which equals `append callee_ctx env.ctx_tm` after iota. If we
       used a literal `context_term env (stream_ctx_of_binders ...)`
       here, F* would refuse the subtyping check at the surrounding
       XLet's body slot because the literal and the Tv_Var differ
       syntactically. *)
    let weakened = `(PXB.weaken #PPS.table #(`#callee_ctx_tm) (`#env.ctx_tm) (`#core_fv_tm)) in
    (* Lower each stream argument in env extended with dummy stream
       binders for preceding args (innermost first). Also build, in
       lockstep, the per-level envs and `__ctx_<N>` extend wraps so
       `wrap_xlets` can pin each interior XLet to a shared named cexp
       context (no per-site implicit `?c` to unify). At each iteration
       we (a) lower the current arg in the env that reflects all
       PRIOR dummies + the prior `__ctx_<N>` chain, (b) call
       `extend_ctx` to mint a fresh `__ctx_<new>` on top of the
       running ctx, and (c) thread that updated env into the next
       iteration. *)
    let rec lower_args (env_running: lower_env)
                       (acc_envs_innermost_first: list lower_env)
                       (acc_wraps_innermost_first: list (T.term -> T.Tac T.term))
                       (defs_innermost_first: list (Ast.sty & T.term))
                       (rem_tys: list Ast.sty)
                       (rem_args: list Ast.ast)
                       : T.Tac (list lower_env & list (Ast.sty & T.term) & list (T.term -> T.Tac T.term)) =
      match rem_tys, rem_args with
      | [], [] ->
        (acc_envs_innermost_first, defs_innermost_first, acc_wraps_innermost_first)
      | sty :: rest_tys, a :: rest_args ->
        let a_tm = lower_stream env_running a in
        let sh = shallow_ty_for_env env_running sty in
        let (env_with_ctx, wrap_here) = extend_ctx env_running sh in
        let dummy_name = "__arg_dummy_" ^ string_of_int (T.fresh ()) in
        let dummy: binder = { b_name = dummy_name; b_sty = sty; b_kind = BStream } in
        let env_next: lower_env = { env_with_ctx with binders = dummy :: env_running.binders } in
        lower_args env_next
                   (env_running :: acc_envs_innermost_first)
                   (wrap_here :: acc_wraps_innermost_first)
                   ((sty, a_tm) :: defs_innermost_first)
                   rest_tys rest_args
      | _, _ ->
        T.fail "Pipit.Source.Ast.Lower: ACallStream arg count mismatch (impossible)"
    in
    let (envs_innermost_first, defs_innermost_first, wraps_innermost_first) =
      lower_args env [] [] [] stream_tys stream_args in
    wrap_xlets envs_innermost_first defs_innermost_first wraps_innermost_first weakened

  | Ast.AFby _r lit e ->
    let e_tm = lower_stream env e in
    exp_XFby env lit.Ast.lit_tm e_tm

  | Ast.ALet _r n m sty def body ->
    (match m with
     | PPI.Stream ->
       let def_tm = lower_stream env def in
       let sh_sty = shallow_ty_for_env env sty in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStream } in
       let (env_ext, wrap) = extend_ctx env sh_sty in
       let env' = env_push b env_ext in
       let body_tm = lower_stream env' body in
       exp_XLet env sh_sty def_tm (wrap body_tm)
     | PPI.Static ->
       (* Bind statically with `let n: sty = def in body` (Tv_Let).
          Earlier we emitted `(fun n -> body) def` so F* would beta-reduce
          during normalisation, but the lambda form forced F* to elaborate
          the body under an abstract binder, drowning the inner cexp's
          implicit `?c` unifications. With explicit-`c` wrappers + a
          shared `__ctx_<N>` ladder this argument no longer applies, and
          `Tv_Let` lets elaboration see the concrete `def` immediately --
          matching the legacy lifter (`git show 129af36~1`). *)
       let def_tm = lower_static env def in
       let nv = fresh_nv n sty in
       let b: binder = { b_name = n; b_sty = sty; b_kind = BStatic nv } in
       let env' = env_push b env in
       let body_tm = lower_stream env' body in
       let letb: T.simple_binder = {
         ppname = R.as_ppname n;
         attrs = [];
         qual = T.Q_Explicit;
         sort = sty;
         uniq = nv.uniq;
       } in
       T.pack (T.Tv_Let false [] letb def_tm body_tm)
     | _ ->
       T.fail ("Pipit.Source.Ast.Lower: ALet with functional mode is not supported: " ^ n))

  | Ast.AMu _r n sty body ->
    let sh_sty = shallow_ty_for_env env sty in
    let b: binder = { b_name = n; b_sty = sty; b_kind = BStream } in
    let (env_ext, wrap) = extend_ctx env sh_sty in
    let env' = env_push b env_ext in
    let body_tm = lower_stream env' body in
    exp_XMu env (wrap body_tm)

  | Ast.ALetMatch r pat scrut_sty scrut_ast body_ast ->
    (* Bind the scrutinee to a fresh name and desugar [pat] into a
       chain of stream ALets over that name; recursively lower the
       resulting AST. The desugaring (projector applications,
       intermediate `_dst#N` names for nested ctor patterns) is in
       [pat_to_alet_chain]. *)
    let scrut_nm: Ast.name = "_scrut#" ^ string_of_int (T.fresh ()) in
    let desugared_body = pat_to_alet_chain r pat scrut_nm scrut_sty body_ast in
    let with_scrut: Ast.ast =
      Ast.ALet r scrut_nm PPI.Stream scrut_sty scrut_ast desugared_body
    in
    lower_stream env with_scrut

  | Ast.AMatch _r am scrut_ast _scrut_sty arms ->
    (* Static-scrutinee multi-arm match. The scrutinee lowers to a
       static F* term; each arm body lowers to a stream `exp` after
       pushing the pattern's binders as STATIC into the env. We emit
       a plain F* `Tv_Match` whose branches return `exp` values --
       at each call site the scrut resolves to a concrete
       constructor and F* normalises the match away. *)
    (match am with
     | Ast.AppPureConst ->
       let scrut_tm = lower_static env scrut_ast in
       let lowered_arms =
         T.map (fun ((pat, body): T.pattern & Ast.ast) ->
           let env_arm = push_static_pat_binders pat env in
           let body_tm = lower_stream env_arm body in
           (pat, body_tm)
         ) arms
       in
       T.pack (T.Tv_Match scrut_tm None lowered_arms)
     | Ast.AppPureStream ->
       T.fail "Pipit.Source.Ast.Lower: AMatch on stream scrutinee is not yet supported")

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
    exp_XCheck env e_tm

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
