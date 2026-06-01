(* Translate an F* term (as a `FStar.Tactics.V2.term`) into the source
   AST in `Pipit.Source.Ast`.

   This is the dual of `Pipit.Source.Ast.Lower`: instead of going
   `ast -> term`, we go `term -> ast`.

   Stage v0
   --------
   Only the subset of F* term forms needed by the simplest source
   programs is supported. Specifically:

   - `Tv_Const`           (int / bool literals)            -> `ALit`
   - `Tv_Var`             (looked up in env)               -> `AVar`
   - `Tv_FVar`            (zero-arity call to a primitive) -> `APrim` with no args
   - `Tv_App` spines      (head is `rec'` / `fby` / FVar)  -> `AMu` / `AFby` / `APrim` / `ACallStream`
   - `Tv_Let false`       (non-recursive let)              -> `ALet`
   - `Tv_Match` of a bool scrutinee with True/False arms
     (i.e. `if-then-else`)                                 -> `APrim AppPureStream` over `PipitRuntime.Prim.p'select`
   - `Tv_Match` of any scrutinee with a SINGLE arm whose
     pattern is irrefutable (variable / wildcard /
     single-constructor data, possibly nested)             -> `ALetMatch` over a Pipit `pat`
   - `Tv_Match` of a STATIC scrutinee with any number of
     arms (data-constructor patterns, etc.)                -> `AMatch AppPureConst`

   General multi-arm pattern matching with a STREAM scrutinee is
   *not* supported in v0. Supporting general stream matches almost
   certainly requires introducing a notion of *clocking* / activation:
   only the substreams under the currently matching arm should
   advance their state. The legacy lift treats stream matches as an
   eager "select" over all branches, which is semantically dubious
   (see the comments in `Pipit.Plugin.Lift`'s `Tv_Match` handler).
   We deliberately do not replicate that here.

   Lambdas (`Tv_Abs`) are stripped *only* at the top level by
   `lift_top_ast`. Lambdas appearing inside a body are unsupported in
   v0 except as the immediate argument of `rec'`.

   Matches, contracts, ascriptions, and `Tv_Let true` (let-rec) are
   currently rejected with a `T.fail`. They will be added later. *)
module Pipit.Source.Ast.Reflect

module T   = FStar.Tactics.V2
module R   = FStar.Range
module Ref = FStar.Reflection.V2
module L   = FStar.List.Tot

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface
module PTB = Pipit.Tactics.Base
module PSAU = Pipit.Source.Ast.Util
module PL  = Pipit.List

(*** Lift environment ***)

(* A binder visible during F* -> AST translation. Each binder has a
   stable AST name derived from its `T.namedv` uniq, so different
   binders with the same surface ppname never collide. *)
noeq
type of_binder = {
  ob_uniq: nat;        (* T.namedv uniq *)
  ob_name: Ast.name;   (* unique string id used in `Ast.AVar` *)
  ob_sty:  Ast.sty;
  ob_mode: PPI.mode;
  (* True iff this binder is one of the top-level explicit params of
     the source binding being lifted, AND mode = Static. Such binders
     are wrapped as `Tv_Abs` around the spliced core sigelt by
     `lift_ast_tac` (preserving the original `T.binder`'s `namedv`),
     so a `Tv_Var` to one of them resolves correctly at splice time.
     All other binders (let-bound locals, pattern binders, top-level
     stream params) are NOT visible at splice point — their lowered
     references use fresh namedvs created by `Lower`. Used by
     `term_safe_at_splice` to decide whether a Static argument can be
     baked into a partial-application prim's `prim_fn`. *)
  ob_top_level: bool;
}

noeq
type of_env = {
  oe_tac_env: T.env;
  oe_binders: list of_binder;        (* innermost first *)
  (* Lifted source bindings known at translation time, with their
     functional mode. `ACallStream` emits one of these. *)
  oe_lifted:  list (Ast.fqn & PPI.mode);
}

let of_empty (tac_env: T.env): of_env =
  { oe_tac_env = tac_env; oe_binders = []; oe_lifted = [] }

(* Push a binder into both the AST-binder list (for `AVar` lookup) and
   the underlying F* tactic environment (so that `Tac.tc` can resolve
   `Tv_Var` references to the binder when we need to recover the type
   of a subterm -- e.g. the return type of an if-then-else branch).
   The synthetic `namedv` reuses the original uniq from `ob_uniq` so
   that `Tv_Var` references match. *)
let of_push (b: of_binder) (e: of_env): of_env =
  let nv: T.namedv = {
    uniq   = b.ob_uniq;
    sort   = FStar.Sealed.seal b.ob_sty;
    ppname = FStar.Sealed.seal b.ob_name;
  } in
  { e with
    oe_binders = b :: e.oe_binders;
    oe_tac_env = Ref.push_namedv e.oe_tac_env (Ref.pack_namedv nv);
  }

let rec of_lookup_uniq (u: nat) (bs: list of_binder): option of_binder =
  match bs with
  | [] -> None
  | b :: rest -> if b.ob_uniq = u then Some b else of_lookup_uniq u rest

let rec of_lookup_lifted (nm: Ast.fqn) (ls: list (Ast.fqn & PPI.mode)): option PPI.mode =
  match ls with
  | [] -> None
  | (fqn, m) :: rest -> if fqn = nm then Some m else of_lookup_lifted nm rest

(* Build a unique AST name from a `T.namedv`. Delegates to
   [Pipit.Source.Ast.Util.mk_uniq_ast_name] so [Lower] uses the same
   convention. *)
let of_name_of_namedv: T.namedv -> T.Tac Ast.name = PSAU.mk_uniq_ast_name

(*** Refinement stripping ***)

(* Recursively replace every `Tv_Refine b _` with `b.sort`, dropping the
   refinement predicate. Applied to types that flow into the core `exp`
   layer (stream-binder sorts, prim argument/result types, ret_ty), which
   doesn't represent dependent / refined types. Static binders that stay
   as ordinary F* `Tv_Abs` wrappers do NOT go through this pass: their
   refinements remain in scope and can mention prior parameters. *)
let strip_refinements_visit (t: T.term): T.Tac T.term =
  match T.inspect t with
  | T.Tv_Refine b _ -> b.sort
  | _ -> t

let strip_refinements: T.term -> T.Tac T.term =
  T.visit_tm strip_refinements_visit

(*** Constants ***)

let of_const (rng: R.range) (c: T.vconst): T.Tac (Ast.lit & PPI.mode) =
  match c with
  | T.C_Int  i ->
    { Ast.lit_ty = `int;  Ast.lit_tm = T.pack (T.Tv_Const (T.C_Int i)) }, PPI.Static
  | T.C_True   ->
    { Ast.lit_ty = `bool; Ast.lit_tm = T.pack (T.Tv_Const T.C_True) },  PPI.Static
  | T.C_False  ->
    { Ast.lit_ty = `bool; Ast.lit_tm = T.pack (T.Tv_Const T.C_False) }, PPI.Static
  | T.C_Unit   ->
    { Ast.lit_ty = `unit; Ast.lit_tm = T.pack (T.Tv_Const T.C_Unit) },  PPI.Static
  | _ ->
    T.fail "Pipit.Source.Ast.Reflect: unsupported constant kind"

(*** Primitives ***)

(* Build an `Ast.prim` from an already-built F* term and a chosen
   `prim_id`. The term must be fully type-resolved (no free uvars or
   ambiguous implicits) so `T.tc` succeeds. Used by
   `of_prim_fv_applied` and by `lift_app_fv`'s partial-application
   path. *)
let of_prim_applied (e: of_env) (prim_id: option Ast.name) (prim_fn: T.term): T.Tac Ast.prim =
  let ty     = T.tc e.oe_tac_env prim_fn in
  let (args, c) = T.collect_arr ty in
  let res_ty = PTB.returns_of_comp c in
  let args   = T.map strip_refinements args in
  let res_ty = strip_refinements res_ty in
  {
    Ast.prim_id;
    Ast.prim_arg_tys = args;
    Ast.prim_ret_ty  = res_ty;
    Ast.prim_fn      = prim_fn;
  }

(* Build an `Ast.prim` from a top-level FVar. The optional `implicits`
   are pre-applied to the head (so e.g. `op_Equality #int` is fully
   instantiated) before typechecking, which lets us recover a
   monomorphic argument-type list. Without this, F* cannot resolve
   implicits like `#a:eqtype` on a bare FVar head and reports them as
   ambiguous. *)
let of_prim_fv_applied (e: of_env) (fv: T.fv) (implicits: list T.argv): T.Tac Ast.prim =
  let nm     = T.inspect_fv fv in
  let nm_str = T.implode_qn nm in
  let fv_tm  = T.pack (T.Tv_FVar fv) in
  let prim_fn =
    match implicits with
    | [] -> fv_tm
    | _  -> T.mk_app fv_tm implicits
  in
  of_prim_applied e (Some nm_str) prim_fn

(* Convenience: no implicits. *)
let of_prim_fv (e: of_env) (fv: T.fv): T.Tac Ast.prim =
  of_prim_fv_applied e fv []

(*** Built-in surface names we recognise ***)

let is_fv_named (fv: T.fv) (qn: string): T.Tac bool =
  Ref.implode_qn (T.inspect_fv fv) = qn

(* Use literal FQN strings instead of `%X` to avoid creating module-level
   dependencies on the modules being recognised. *)
let fqn_rec'  : string = "Pipit.Plugin.Interface.rec'"
let fqn_fby   : string = "Pipit.Source.fby"
let fqn_check : string = "Pipit.Source.check"

(*** Main translation ***)

val lift_tm (e: of_env) (t: T.term): T.Tac (PPI.mode & Ast.ast)

(* Drop F* implicit arguments from an argument list. We treat type and
   typeclass implicits as unsupported in the lifted body — they are
   resolved at splice time, not lifted into the AST. *)
let drop_implicits (args: list T.argv): list T.argv =
  L.filter (fun (_, q) -> Ref.Q_Explicit? q) args

(* Determine the application mode of an `APrim`: pure-stream if any
   argument is a stream, pure-const otherwise. *)
let app_mode_of (margs: list (PPI.mode & Ast.ast)): PPI.mode & Ast.app_mode =
  let any_stream =
    L.existsb (fun (m, _) -> match m with | PPI.Stream -> true | _ -> false) margs
  in
  if any_stream
  then PPI.Stream, Ast.AppPureStream
  else PPI.Static, Ast.AppPureConst

(*** Irrefutable pattern matching helpers ===

   `let (a, b) = scrut in body` and friends. F* desugars these to a
   `Tv_Match` with a single arm whose pattern is a constructor pattern
   wrapping variable binders. We translate the F* pattern into an
   `Ast.pat` (PWild / PVar / PCon) and emit an `Ast.ALetMatch`; the
   `Pipit.Source.Ast.Lower` pass walks the `Ast.pat` and emits the
   corresponding chain of `XLet`s with projector applications.

   This walker is responsible for:

   * computing each `PVar`'s source type (taken from the parent
     constructor's field projector's return type), and
   * pushing each `PVar` into the lift env so that the body lifts
     correctly under the new binders.

   The scheme handles tuples (which desugar to `Mktuple2`/`Mktuple3`/...),
   records (single-constructor data types whose field projectors share
   field names), and any single-constructor data type. Multi-arm
   matches and refutable patterns are not yet supported. *)

(* Strip implicit subpats; keep explicit ones in order. *)
let rec explicit_subpats (ss: list (T.pattern & bool)): list T.pattern =
  match ss with
  | [] -> []
  | (_, true) :: rest -> explicit_subpats rest
  | (p, false) :: rest -> p :: explicit_subpats rest

(* Pattern size metric used to prove termination of [bind_pat] /
   [bind_pat_ctor]. Every node and every cons-cell in subpat lists
   contributes 1, so any strict sub-pattern / sub-list strictly
   decreases the metric. *)
let rec pat_size (p: T.pattern): nat =
  match p with
  | T.Pat_Cons pc -> 1 + bool_subpats_size pc.subpats
  | _ -> 1

and bool_subpats_size (ss: list (T.pattern & bool)): nat =
  match ss with
  | [] -> 0
  | (p, _) :: rest -> 1 + pat_size p + bool_subpats_size rest

let rec subpats_size (ss: list T.pattern): nat =
  match ss with
  | [] -> 0
  | p :: rest -> 1 + pat_size p + subpats_size rest

(* [subpats_size (explicit_subpats ss) <= bool_subpats_size ss]. Used
   by [bind_pat]'s [Pat_Cons] case so its call to [bind_pat_ctor]
   strictly decreases. *)
let rec explicit_subpats_size_lemma (ss: list (T.pattern & bool))
  : Lemma (subpats_size (explicit_subpats ss) <= bool_subpats_size ss)
=
  match ss with
  | [] -> ()
  | (_, true)  :: rest -> explicit_subpats_size_lemma rest
  | (_, false) :: rest -> explicit_subpats_size_lemma rest

(* Pattern is irrefutable iff every leaf is a variable / wildcard and
   every constructor node is irrefutable in its explicit subpats.
   ([Pat_Var] covers both variable bindings and wildcards in
   reflection.) Implicit subpats are skipped -- they're resolved by
   elaboration. *)
let rec is_pat_irref (p: T.pattern): bool =
  match p with
  | T.Pat_Var _ -> true
  | T.Pat_Cons pc -> is_pat_irref_subs pc.subpats
  | _ -> false

and is_pat_irref_subs (ss: list (T.pattern & bool)): bool =
  match ss with
  | [] -> true
  | (_, true)  :: rest -> is_pat_irref_subs rest
  | (p, false) :: rest -> if is_pat_irref p then is_pat_irref_subs rest else false

(* Detect the bool-scrutinee if-then-else shape that [lift_ite]
   handles. F* desugars `if c then t else e` as `match c with
   | true -> t | _ -> e` (the false-case is typically a wildcard
   `Pat_Var uu___`, not `Pat_Constant C_False`). We accept either
   order and tolerate a wildcard / variable in the catch-all branch.
   Multi-arm matches that do NOT match this shape go to
   [lift_match_general]. *)
let is_ite_shape (brs: list T.branch): bool =
  match brs with
  | [(T.Pat_Constant { c = T.C_True  }, _); (_, _)] -> true
  | [(T.Pat_Constant { c = T.C_False }, _); (_, _)] -> true
  | [(_, _); (T.Pat_Constant { c = T.C_False }, _)] -> true
  | [(_, _); (T.Pat_Constant { c = T.C_True  }, _)] -> true
  | _ -> false

(* Pattern/constructor helpers are shared with [Lower] -- see
   [Pipit.Source.Ast.Util]. *)
let ctor_field_names: T.env -> T.fv -> T.Tac (list Ast.name) = PSAU.ctor_field_names
let scrut_type_implicits: T.term -> T.Tac (list T.argv) = PSAU.scrut_type_implicits
let projector_fqn: Ast.fqn -> Ast.name -> T.Tac Ast.fqn = PSAU.projector_fqn

(* Walk an irrefutable F* pattern; produce a Pipit `Ast.pat` and
   extend the lift env with one binder per leaf [Pat_Var]. The
   [parent_ty] is the source type of the (sub)value being matched
   against this (sub)pattern; for a top-level call this is the
   scrutinee's type, and for a sub-call it is the corresponding
   field's type as recovered from the parent constructor's
   projector. The [binder_mode] selects whether bound vars are pushed
   into the env as `Stream` (for `ALetMatch` over a stream scrutinee)
   or `Static` (for `AMatch AppPureConst` over a static scrutinee). *)
let rec pat_of_fstar (e: of_env) (binder_mode: PPI.mode)
                     (pat: T.pattern) (parent_ty: Ast.sty)
    : T.Tac (of_env & Ast.pat)
      (decreases (pat_size pat))
=
  match pat with
  | T.Pat_Var bv ->
    let nm = of_name_of_namedv bv.v in
    let ob: of_binder = {
      ob_uniq = bv.v.uniq;
      ob_name = nm;
      ob_sty  = parent_ty;
      ob_mode = binder_mode;
      ob_top_level = false;
    } in
    of_push ob e, Ast.PVar nm parent_ty binder_mode

  | T.Pat_Cons pc ->
    let ctor_fqn = T.inspect_fv pc.head in
    let field_names = ctor_field_names e.oe_tac_env pc.head in
    let exp_subs = explicit_subpats pc.subpats in
    (if L.length field_names <> L.length exp_subs then
      T.fail "Pipit.Source.Ast.Reflect: pattern arity mismatch (explicit subpats vs ctor fields)"
     else ());
    let implicits = scrut_type_implicits parent_ty in
    explicit_subpats_size_lemma pc.subpats;
    let (e', sub_pats) =
      pat_of_fstar_subs e binder_mode ctor_fqn field_names exp_subs implicits
    in
    e', Ast.PCon ctor_fqn sub_pats

  | T.Pat_Dot_Term _ ->
    e, Ast.PWild

  | _ ->
    T.fail "Pipit.Source.Ast.Reflect: unsupported irrefutable pattern shape"

and pat_of_fstar_subs (e: of_env) (binder_mode: PPI.mode)
                       (ctor_fqn: Ast.fqn)
                       (fields: list Ast.name) (subs: list T.pattern)
                       (implicits: list T.argv)
    : T.Tac (of_env & list Ast.pat)
      (decreases (subpats_size subs))
=
  match fields, subs with
  | [], [] -> e, []
  | f :: fs, p :: ps ->
    let proj_fqn = projector_fqn ctor_fqn f in
    let proj_fv  = T.pack_fv proj_fqn in
    let proj_prim = of_prim_fv_applied e proj_fv implicits in
    let field_ty: Ast.sty = proj_prim.Ast.prim_ret_ty in
    let (e', sub_pat) = pat_of_fstar e binder_mode p field_ty in
    let (e'', rest) = pat_of_fstar_subs e' binder_mode ctor_fqn fs ps implicits in
    e'', sub_pat :: rest
  | _, _ ->
    T.fail "Pipit.Source.Ast.Reflect: pattern/field arity mismatch (impossible)"

(* Decide whether an F* term can be safely baked into a partial-
   application prim's `prim_fn` at splice point. Safe iff every
   `Tv_Var` reference resolves to either a pass-through binder (not
   in `oe_binders` \u2014 they are bound by the outer `Tv_Abs` wrappers
   that `lift_ast_tac` puts around the spliced sigelt) or a
   top-level Static explicit param (`ob_top_level = true` \u2014 these
   also get a `Tv_Abs` wrapper, with the original `T.binder`'s
   `namedv` preserved). Local let-bound and pattern binders are not
   F*-visible at splice point (`Lower` allocates fresh namedvs for
   them), so referencing them is unsafe.

   For complex shapes (Abs/Arrow/Let/Match/Refine) we conservatively
   return `false` to avoid binder-tracking. Static-mode argument
   terms in practice are simple (vars, fvar, app, const), so the
   conservative cases rarely fire. *)
let rec term_safe_at_splice (e: of_env) (t: T.term): T.Tac bool =
  match T.inspect t with
  | T.Tv_Var nv ->
    (match of_lookup_uniq nv.uniq e.oe_binders with
     | None    -> true
     | Some ob -> ob.ob_top_level)
  | T.Tv_Const _    -> true
  | T.Tv_FVar _     -> true
  | T.Tv_UInst _ _  -> true
  | T.Tv_Type _     -> true
  | T.Tv_BVar _     -> true
  | T.Tv_App hd (arg, _) ->
    if term_safe_at_splice e hd then term_safe_at_splice e arg else false
  | T.Tv_AscribedT t' _ _ _ -> term_safe_at_splice e t'
  | T.Tv_AscribedC t' _ _ _ -> term_safe_at_splice e t'
  | _ -> false

let rec lift_tm e t =
  let rng: R.range = Ref.range_of_term t in
  match T.inspect t with
  | T.Tv_Const c ->
    let (lit, m) = of_const rng c in
    m, Ast.ALit rng lit

  | T.Tv_Var nv ->
    (match of_lookup_uniq nv.uniq e.oe_binders with
     | Some b -> b.ob_mode, Ast.AVar rng b.ob_name b.ob_mode
     | None ->
       T.fail ("Pipit.Source.Ast.Reflect: free variable not in lift env: " ^
               T.unseal nv.ppname))

  | T.Tv_FVar fv ->
    (* Zero-arity FVar: treat as an unapplied primitive (or call). For
       v0 we just emit `APrim AppPureConst` with no args. *)
    let prim = of_prim_fv e fv in
    PPI.Static, Ast.APrim rng Ast.AppPureConst prim []

  | T.Tv_App _ _ ->
    let (hd, args) = T.collect_app t in
    let implicits = L.filter (fun (_, q) -> not (Ref.Q_Explicit? q)) args in
    let explicits = drop_implicits args in
    lift_app e rng hd implicits explicits

  | T.Tv_Let false attrs b def body ->
    let (mdef, def_ast) = lift_tm e def in
    let sty: Ast.sty = b.sort in
    let ob: of_binder = {
      ob_uniq = b.uniq;
      ob_name = of_name_of_namedv (T.binder_to_namedv b);
      ob_sty  = sty;
      ob_mode = mdef;
      ob_top_level = false;
    } in
    let e' = of_push ob e in
    let (mbody, body_ast) = lift_tm e' body in
    mbody, Ast.ALet rng ob.ob_name mdef sty def_ast body_ast

  | T.Tv_AscribedT inner _ _ _ ->
    lift_tm e inner

  | T.Tv_AscribedC inner _ _ _ ->
    lift_tm e inner

  | T.Tv_Match scrut _ret brs ->
    (match brs with
     | [(pat, body)] ->
       if is_pat_irref pat
       then lift_match_irref e rng scrut pat body
       else if is_ite_shape brs
       then lift_ite e rng scrut brs
       else lift_match_general e rng scrut brs
     | _ ->
       if is_ite_shape brs
       then lift_ite e rng scrut brs
       else lift_match_general e rng scrut brs)

  | _ ->
    T.fail ("Pipit.Source.Ast.Reflect: unsupported term shape: " ^
            T.term_to_string t)

(* Lift an application `hd args` with implicits already partitioned
   out. `implicits` is the list of implicit arguments (in source
   order, original qualifier preserved) so the prim head can be
   pre-applied to resolve type variables; `args` is the explicit
   spine. *)
and lift_app (e: of_env) (rng: R.range) (hd: T.term) (implicits: list T.argv) (args: list T.argv): T.Tac (PPI.mode & Ast.ast) =
  match T.inspect hd with
  | T.Tv_FVar fv
  | T.Tv_UInst fv _ ->
    let fqn_s = Ref.implode_qn (T.inspect_fv fv) in
    if fqn_s = fqn_rec'
    then lift_app_rec e rng args
    else if fqn_s = fqn_fby
    then lift_app_fby e rng args
    else if fqn_s = fqn_check
    then lift_app_check e rng args
    else lift_app_fv e rng fv implicits args
  | _ ->
    T.fail ("Pipit.Source.Ast.Reflect: application head not supported: " ^
            T.term_to_string hd)

and lift_app_rec (e: of_env) (rng: R.range) (args: list T.argv): T.Tac (PPI.mode & Ast.ast) =
  match args with
  | [(arg, _)] ->
    (match T.inspect arg with
     | T.Tv_Abs b body ->
       let sty: Ast.sty = b.sort in
       let nm = of_name_of_namedv (T.binder_to_namedv b) in
       let ob: of_binder = {
         ob_uniq = b.uniq;
         ob_name = nm;
         ob_sty  = sty;
         ob_mode = PPI.Stream;
         ob_top_level = false;
       } in
       let e' = of_push ob e in
       let (_, body_ast) = lift_tm e' body in
       PPI.Stream, Ast.AMu rng nm sty body_ast
     | _ ->
       T.fail "Pipit.Source.Ast.Reflect: rec' applied to non-lambda")
  | _ ->
    T.fail "Pipit.Source.Ast.Reflect: rec' expects exactly one explicit argument"

and lift_app_fby (e: of_env) (rng: R.range) (args: list T.argv): T.Tac (PPI.mode & Ast.ast) =
  match args with
  | [(v_tm, _); (e_tm, _)] ->
    let (v_mode, _v_ast) = lift_tm e v_tm in
    (match v_mode with
     | PPI.Static ->
       let v_ty = strip_refinements (T.tc e.oe_tac_env v_tm) in
       let lit: Ast.lit = { Ast.lit_ty = v_ty; Ast.lit_tm = v_tm } in
       let (_, e_ast) = lift_tm e e_tm in
       PPI.Stream, Ast.AFby rng lit e_ast
     | _ ->
       T.fail "Pipit.Source.Ast.Reflect: fby init must be a static value")
  | _ ->
    T.fail "Pipit.Source.Ast.Reflect: fby expects two explicit arguments"

and lift_app_check (e: of_env) (rng: R.range) (args: list T.argv): T.Tac (PPI.mode & Ast.ast) =
  match args with
  | [(prop_tm, _)] ->
    let (_, prop_ast) = lift_tm e prop_tm in
    PPI.Stream, Ast.ACheck rng None prop_ast
  | _ ->
    T.fail "Pipit.Source.Ast.Reflect: check expects exactly one explicit argument"

(* Lift an irrefutable single-arm match [match scrut with | pat -> body].
   Walk the F* pattern into an [Ast.pat] (which also extends the lift
   env with the bound names), lift the body in the extended env, and
   emit [ALetMatch]. The Lower pass walks [Ast.pat] and emits the
   corresponding chain of [XLet]s with projector applications. *)
and lift_match_irref (e: of_env) (rng: R.range) (scrut: T.term)
                     (pat: T.pattern) (body: T.term)
    : T.Tac (PPI.mode & Ast.ast) =
  let (m_scrut, scrut_ast) = lift_tm e scrut in
  (match m_scrut with
   | PPI.Stream -> ()
   | _ ->
     T.fail "Pipit.Source.Ast.Reflect: irrefutable match on non-stream scrutinee is not yet supported");
  let scrut_ty: Ast.sty = T.tc e.oe_tac_env scrut in
  let (e_after, pipit_pat) = pat_of_fstar e PPI.Stream pat scrut_ty in
  let (m_body, body_ast) = lift_tm e_after body in
  m_body, Ast.ALetMatch rng pipit_pat scrut_ty scrut_ast body_ast

(* Recognise the if-then-else shape:
     `Tv_Match scrut [(Pat_Constant C_True, t); (Pat_Constant C_False, e)]`
   (or the same with the True/False branches swapped). Other match
   shapes are rejected here in v0.

   Lowered as `APrim AppPureStream` over `PipitRuntime.Prim.p'select`,
   which is just `fun cond t f -> if cond then t else f`. This means
   *both* branches are evaluated and their substreams advance every
   cycle, regardless of the scrutinee. That is fine for pure if-then-
   else over arithmetic / bool / record values, but it is the same
   semantically-dubious "select" the legacy lift uses for general
   matches. A correct implementation of multi-arm pattern matches
   (especially on data constructors with stream substreams) likely
   needs to introduce a notion of *clocking* / activation so that
   substreams under a non-matching arm do not advance their state.
   That is out of scope for v0 -- if-then-else is enough for the
   currently-active `#lang-pipit` examples. *)
and lift_ite (e: of_env) (rng: R.range) (scrut: T.term) (brs: list T.branch): T.Tac (PPI.mode & Ast.ast) =
  (* F* desugars `if c then t else e` as `match c with | true -> t | _ -> e`
     (the false-case is typically a wildcard `Pat_Var uu___`, not
     `Pat_Constant C_False`). We accept either order and tolerate a
     wildcard / variable in the catch-all branch (we do not bind from
     it -- the scrutinee value is determined by the chosen arm). *)
  let (t_tm, f_tm) =
    match brs with
    | [(T.Pat_Constant { c = T.C_True  }, t); (_, f)] -> (t, f)
    | [(T.Pat_Constant { c = T.C_False }, f); (_, t)] -> (t, f)
    | [(_, t); (T.Pat_Constant { c = T.C_False }, f)] -> (t, f)
    | [(_, f); (T.Pat_Constant { c = T.C_True  }, t)] -> (t, f)
    | _ ->
      T.fail ("Pipit.Source.Ast.Reflect: lift_ite called on non-ite shape (impossible: dispatch checks is_ite_shape)")
  in
  let (mc, c_ast) = lift_tm e scrut in
  let (mt, t_ast) = lift_tm e t_tm in
  let (mf, f_ast) = lift_tm e f_tm in
  let ret_ty: T.term = T.tc e.oe_tac_env t_tm in
  let bool_ty: T.term = `bool in
  let p_select_fv =
    T.pack (T.Tv_FVar (T.pack_fv ["PipitRuntime"; "Prim"; "p'select"]))
  in
  let prim_fn: T.term =
    T.mk_app p_select_fv [(ret_ty, T.Q_Implicit)]
  in
  let prim: Ast.prim = {
    Ast.prim_id      = Some "PipitRuntime.Prim.p'select";
    Ast.prim_arg_tys = [bool_ty; ret_ty; ret_ty];
    Ast.prim_ret_ty  = ret_ty;
    Ast.prim_fn      = prim_fn;
  } in
  let margs = [(mc, c_ast); (mt, t_ast); (mf, f_ast)] in
  let (rm, am) = app_mode_of margs in
  rm, Ast.APrim rng am prim [c_ast; t_ast; f_ast]

(* General multi-arm `match scrut with | p1 -> b1 | ... | pN -> bN`.
   v0 only supports a STATIC scrutinee (the static value resolves to
   a concrete constructor at each call site, so the match folds away
   during F* elaboration). Stream scrutinees would need a runtime
   dispatch and are not yet supported (see `AMatch` doc in Ast.fst).

   For each arm we walk the pattern with [pat_of_fstar] in mode
   `Static` (to push pattern binders as static into the lift env)
   and lift the body in the extended env. The original F* pattern is
   carried in the [AMatch] arm so that `Lower` can re-emit it verbatim
   under a plain F* `Tv_Match`. *)
and lift_match_general (e: of_env) (rng: R.range) (scrut: T.term)
                       (brs: list T.branch): T.Tac (PPI.mode & Ast.ast) =
  let (m_scrut, scrut_ast) = lift_tm e scrut in
  (match m_scrut with
   | PPI.Static -> ()
   | _ ->
     T.fail "Pipit.Source.Ast.Reflect: multi-arm match on non-static scrutinee is not yet supported");
  let scrut_ty: Ast.sty = T.tc e.oe_tac_env scrut in
  let arms: list (T.pattern & Ast.ast) =
    T.map (fun ((pat, body): T.branch) ->
      let (e_arm, _pipit_pat) = pat_of_fstar e PPI.Static pat scrut_ty in
      let (_m_body, body_ast) = lift_tm e_arm body in
      (pat, body_ast)
    ) brs
  in
  PPI.Stream, Ast.AMatch rng Ast.AppPureConst scrut_ast scrut_ty arms

and lift_app_fv (e: of_env) (rng: R.range) (fv: T.fv) (implicits: list T.argv) (args: list T.argv): T.Tac (PPI.mode & Ast.ast) =
  let fqn = T.inspect_fv fv in
  let margs = lift_args e args in
  let arg_asts = L.map snd margs in
  match of_lookup_lifted fqn e.oe_lifted with
  | Some m_lifted ->
    (* Another `#lang-pipit` binding: stream-aware call. Resolve the
       callee's source signature so that `Lower` can build the
       `XLet`/`weaken` chain without re-typechecking.

       For polymorphic callees we must pre-apply the call-site
       implicits (resolved by F* when elaborating the user-facing
       call) to the FVar before `T.tc`, so that free type variables
       like `#a` in `fst (#a #b: eqtype) ...` are replaced with
       concrete types (`int`, `bool`, ...). Without this, `arg_tys`
       would still mention the callee's type variables, which are not
       in scope at the call site and break `Lower.context_term`.
       Mirrors `of_prim_fv_applied`. *)
    let fv_tm = T.pack (T.Tv_FVar fv) in
    let head_applied =
      match implicits with
      | [] -> fv_tm
      | _  -> T.mk_app fv_tm implicits
    in
    let src_ty = T.tc e.oe_tac_env head_applied in
    let (arg_bs, _) = T.collect_arr_bs src_ty in
    let explicit_bs =
      L.filter (fun (b: T.binder) -> Ref.Q_Explicit? b.qual) arg_bs
    in
    let arg_tys: list Ast.sty = L.map (fun (b: T.binder) -> b.sort) explicit_bs in
    let br: Ast.binding_ref = {
      Ast.br_fqn       = fqn;
      Ast.br_mode      = m_lifted;
      Ast.br_arg_tys   = arg_tys;
      Ast.br_implicits = implicits;
    } in
    PPI.Stream, Ast.ACallStream rng br arg_asts
  | None ->
    (* Pre-apply the leading run of Static-mode, splice-safe args to
       the FVar. Without this, the prim's `arg_tys` would contain
       every static arg's source type, and `Lower.funty_of` would
       call `shallow_ty` on each — failing on non-eqtype records
       (TTCan's `config`, anything with function fields). Trailing
       static args after the first stream arg (or the first
       splice-unsafe static arg) go through the existing path
       unchanged (they would need eta expansion to fold in).

       A static arg is splice-safe iff its F* term has no free refs
       to local non-top-level binders — see `term_safe_at_splice`.
       Local let bindings push Static-mode binders into `oe_binders`
       (e.g. `let strm: stream int = 1 in ...` makes `strm` Static
       because `1` is a Static const), but their F* `namedv` is only
       re-bound by `Lower` inside the lowered body, not at splice
       top — so embedding a `Tv_Var` to one of them in `prim_fn`
       would dangle.

       CSE caveat: `Pipit.Prim.Shallow.axiom_prim_eq` says two prims
       with the same `prim_id` have the same `prim_ty` and
       `prim_sem`. A partially-applied prim bakes its statics into
       `prim_fn`, so two distinct callsites with the same FQN may
       disagree on `prim_sem`. We set `prim_id = None` whenever
       anything is pre-applied — `prim_eq` returns `false` on `None`
       so CSE safely skips these. Fully-applied calls keep their
       `Some nm_str` id and remain CSE-eligible. *)
    let zipped: list ((PPI.mode & Ast.ast) & T.argv) = PL.zip2 margs args in
    (* Pre-compute splice safety in Tac, then split with a pure
       predicate (split_prefix is Tot, can't host a Tac body). *)
    let tagged: list (bool & ((PPI.mode & Ast.ast) & T.argv)) =
      T.map (fun (mz: (PPI.mode & Ast.ast) & T.argv) ->
        let ((m, _), (a, _)) = mz in
        let safe = PPI.Static? m && term_safe_at_splice e a in
        (safe, mz)) zipped
    in
    let (pre_static_t, rest_t) =
      PL.split_prefix (fun (x: bool & ((PPI.mode & Ast.ast) & T.argv)) -> fst x) tagged
    in
    let pre_static_z: list ((PPI.mode & Ast.ast) & T.argv) = L.map snd pre_static_t in
    let rest_z: list ((PPI.mode & Ast.ast) & T.argv) = L.map snd rest_t in
    let pre_static_argv: list T.argv = L.map snd pre_static_z in
    let rest_margs: list (PPI.mode & Ast.ast) = L.map fst rest_z in
    let rest_arg_asts: list Ast.ast = L.map snd rest_margs in
    let fv_tm = T.pack (T.Tv_FVar fv) in
    let head_args = L.append implicits pre_static_argv in
    let prim_fn =
      match head_args with
      | [] -> fv_tm
      | _  -> T.mk_app fv_tm head_args
    in
    let prim_id: option Ast.name =
      match pre_static_argv with
      | [] -> Some (T.implode_qn (T.inspect_fv fv))
      | _  -> None
    in
    let prim = of_prim_applied e prim_id prim_fn in
    let (rm, am) = app_mode_of rest_margs in
    rm, Ast.APrim rng am prim rest_arg_asts

and lift_args (e: of_env) (args: list T.argv): T.Tac (list (PPI.mode & Ast.ast)) =
  match args with
  | [] -> []
  | (a, _) :: rest ->
    let res = lift_tm e a in
    res :: lift_args e rest

(*** Top-level entry ***)

(* Lift a top-level source binding's body. Strips off explicit lambdas,
   pushing each parameter as a `Stream` binder, then lifts the body.

   Polymorphic / instance binders (anything with a non-`Q_Explicit`
   qualifier — type parameters like `#a: eqtype`, typeclass instances
   like `{| has_stream a |}`, etc.) are passed through verbatim: they
   are NOT given de Bruijn indices in the AST, but they ARE pushed
   into the underlying `T.env` so that `T.tc` lookups for terms that
   mention them still resolve. The caller (`lift_ast_tac`) wraps the
   synthesised core sigelt back in `Tv_Abs` / `Tv_Arrow` for each
   pass-through binder so the spliced binding remains polymorphic.

   Returns the pass-through binders (outermost first, source order),
   the explicit params paired with their original `T.binder`
   (source order, outermost first), the inferred return type of the
   body (typed against the env that contains the pass-through +
   explicit binders, so any `Tv_Var` references use the uniqs from
   `lb_def` — NOT `lb_typ` — and remain resolvable when wrapped back
   up by the caller), and the lifted AST body. Each explicit binder's
   mode is recovered from `lb_mode` (one `ModeFun` layer per binder,
   in `T.collect_abs` order). *)
let lift_top_body (tac_env: T.env) (lifted: list (Ast.fqn & PPI.mode))
                  (lb_mode: PPI.mode) (body: T.term)
  : T.Tac (list T.binder & list (T.binder & of_binder) & T.term & Ast.ast)
=
  let (bs, body) = T.collect_abs body in
  let e0: of_env = { oe_tac_env = tac_env; oe_binders = []; oe_lifted = lifted } in
  (* Walk binders in source order, peeling one `ModeFun` layer per
     binder to recover its declared mode. `lb_mode` is produced by the
     `#lang-pipit` preprocessor (see `Pipit.Plugin.Support.mode_of_pattern`)
     and contains one `ModeFun` layer per binder in `T.collect_abs`
     order, regardless of explicitness. We fall back to `Stream` if
     `lb_mode` is exhausted (defensive — shouldn't happen for
     well-formed source bindings). The explicit-param accumulator
     pairs each `of_binder` with its original `T.binder` so callers
     can rebuild it (e.g. for wrapping static params as F* `Tv_Abs`
     around the spliced sigelt). *)
  let push_param (acc: of_env & list T.binder & list (T.binder & of_binder) & PPI.mode)
                 (b: T.binder)
    : T.Tac (of_env & list T.binder & list (T.binder & of_binder) & PPI.mode)
  =
    let (e, passthrough_rev, explicits_rev, m) = acc in
    let (arg_mode, rest_mode): PPI.mode & PPI.mode = match m with
      | PPI.ModeFun am _ rm -> (am, rm)
      | _ -> (PPI.Stream, m)
    in
    if Ref.Q_Explicit? b.qual then
      let nm = of_name_of_namedv (T.binder_to_namedv b) in
      let ob: of_binder = {
        ob_uniq = b.uniq;
        ob_name = nm;
        ob_sty  = strip_refinements b.sort;
        ob_mode = arg_mode;
        (* Only Static top-level params get a `Tv_Abs` wrapper from
           `lift_ast_tac`; stream params become cexp ctx binders. *)
        ob_top_level = (arg_mode = PPI.Static);
      } in
      (of_push ob e, passthrough_rev, (b, ob) :: explicits_rev, rest_mode)
    else
      (* Pass-through (type / instance / proof) binder. Push into the
         tac env only — no AST binder, no de Bruijn slot. *)
      let nv = T.binder_to_namedv b in
      let e' = { e with oe_tac_env = Ref.push_namedv e.oe_tac_env (Ref.pack_namedv nv) } in
      (e', b :: passthrough_rev, explicits_rev, rest_mode)
  in
  let (e_final, passthrough_rev, explicits_rev, _) =
    T.fold_left push_param (e0, [], [], lb_mode) bs in
  let ret_ty: T.term = strip_refinements (T.tc e_final.oe_tac_env body) in
  let (_, ast) = lift_tm e_final body in
  (L.rev passthrough_rev, L.rev explicits_rev, ret_ty, ast)
