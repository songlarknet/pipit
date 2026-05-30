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
     single-constructor data, possibly nested)             -> `ALet` chain of projector applications

   General multi-arm pattern matching (data-constructor scrutinees,
   multi-arm matches with variable patterns, refutable patterns) is
   *not* supported in v0. Even for the eventual implementation,
   supporting general stream matches almost certainly requires
   introducing a notion of *clocking* / activation: only the substreams
   under the currently matching arm should advance their state. The
   legacy lift treats stream matches as an eager "select" over all
   branches, which is semantically dubious (see the comments in
   `Pipit.Plugin.Lift`'s `Tv_Match` handler). We deliberately do not
   replicate that here.

   Lambdas (`Tv_Abs`) are stripped *only* at the top level by
   `lift_top_ast`. Lambdas appearing inside a body are unsupported in
   v0 except as the immediate argument of `rec'`.

   Matches, contracts, ascriptions, and `Tv_Let true` (let-rec) are
   currently rejected with a `T.fail`. They will be added later. *)
module Pipit.Source.Ast.OfFStar

module T   = FStar.Tactics.V2
module R   = FStar.Range
module Ref = FStar.Reflection.V2
module L   = FStar.List.Tot

module Ast = Pipit.Source.Ast
module PPI = Pipit.Plugin.Interface
module PTB = Pipit.Tactics.Base

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

(* Build a unique AST name from a `T.namedv`. The uniq is part of the
   string so distinct binders with the same surface ppname don't clash. *)
let of_name_of_namedv (nv: T.namedv): T.Tac Ast.name =
  let ppname = T.unseal nv.ppname in
  ppname ^ "#" ^ string_of_int nv.uniq

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
    T.fail "Pipit.Source.Ast.OfFStar: unsupported constant kind"

(*** Primitives ***)

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
  let ty     = T.tc e.oe_tac_env prim_fn in
  let (args, c) = T.collect_arr ty in
  let res_ty = PTB.returns_of_comp c in
  let args   = T.map strip_refinements args in
  let res_ty = strip_refinements res_ty in
  {
    Ast.prim_id      = Some nm_str;
    Ast.prim_arg_tys = args;
    Ast.prim_ret_ty  = res_ty;
    Ast.prim_fn      = prim_fn;
  }

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

(* For a data constructor [ctor], return the ppnames of its explicit
   binders -- exactly the field names used by F*'s auto-generated
   projectors ([Mktuple2?._1], [Mkpoint?.px], [Some?.v], etc.). *)
let ctor_field_names (env: T.env) (ctor_fv: T.fv): T.Tac (list Ast.name) =
  let ctor_tm = T.pack (T.Tv_FVar ctor_fv) in
  let ctor_ty = T.tc env ctor_tm in
  let (bs, _) = T.collect_arr_bs ctor_ty in
  let explicit_bs =
    L.filter (fun (b: T.binder) -> Ref.Q_Explicit? b.qual) bs
  in
  T.map (fun (b: T.binder) -> T.unseal b.ppname) explicit_bs

(* Recover the implicit type arguments threaded through a constructor
   and its projectors. For a scrutinee of type [tuple2 int int], the
   head is the type constructor and the args are [int; int]; we
   re-tag them as implicit so they instantiate the projector's
   [#a:Type -> #b:Type -> ...] binders. *)
let scrut_type_implicits (scrut_ty: T.term): T.Tac (list T.argv) =
  let (_, ty_args) = T.collect_app scrut_ty in
  T.map (fun (a: T.argv) -> let (t, _) = a in (t, T.Q_Implicit)) ty_args

(* Compute the projector FQN for an explicit constructor field. F*'s
   auto-generated projectors are named [__proj__<Ctor>__item__<field>]
   in the same module as the constructor. *)
let projector_fqn (ctor_fqn: Ast.fqn) (field: Ast.name): T.Tac Ast.fqn =
  match L.rev ctor_fqn with
  | [] -> T.fail "Pipit.Source.Ast.OfFStar: empty constructor FQN"
  | ctor_nm :: rest_rev ->
    let proj_nm = "__proj__" ^ ctor_nm ^ "__item__" ^ field in
    L.rev (proj_nm :: rest_rev)

(* Walk an irrefutable F* pattern; produce a Pipit `Ast.pat` and
   extend the lift env with one binder per leaf [Pat_Var]. The
   [parent_ty] is the source type of the (sub)value being matched
   against this (sub)pattern; for a top-level call this is the
   scrutinee's type, and for a sub-call it is the corresponding
   field's type as recovered from the parent constructor's
   projector. *)
let rec pat_of_fstar (e: of_env) (pat: T.pattern) (parent_ty: Ast.sty)
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
      ob_mode = PPI.Stream;
    } in
    of_push ob e, Ast.PVar nm parent_ty PPI.Stream

  | T.Pat_Cons pc ->
    let ctor_fqn = T.inspect_fv pc.head in
    let field_names = ctor_field_names e.oe_tac_env pc.head in
    let exp_subs = explicit_subpats pc.subpats in
    (if L.length field_names <> L.length exp_subs then
      T.fail "Pipit.Source.Ast.OfFStar: pattern arity mismatch (explicit subpats vs ctor fields)"
     else ());
    let implicits = scrut_type_implicits parent_ty in
    explicit_subpats_size_lemma pc.subpats;
    let (e', sub_pats) =
      pat_of_fstar_subs e ctor_fqn field_names exp_subs implicits
    in
    e', Ast.PCon ctor_fqn sub_pats

  | T.Pat_Dot_Term _ ->
    e, Ast.PWild

  | _ ->
    T.fail "Pipit.Source.Ast.OfFStar: unsupported irrefutable pattern shape"

and pat_of_fstar_subs (e: of_env) (ctor_fqn: Ast.fqn)
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
    let (e', sub_pat) = pat_of_fstar e p field_ty in
    let (e'', rest) = pat_of_fstar_subs e' ctor_fqn fs ps implicits in
    e'', sub_pat :: rest
  | _, _ ->
    T.fail "Pipit.Source.Ast.OfFStar: pattern/field arity mismatch (impossible)"

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
       T.fail ("Pipit.Source.Ast.OfFStar: free variable not in lift env: " ^
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
       else lift_ite e rng scrut brs
     | _ ->
       lift_ite e rng scrut brs)

  | _ ->
    T.fail ("Pipit.Source.Ast.OfFStar: unsupported term shape: " ^
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
    T.fail ("Pipit.Source.Ast.OfFStar: application head not supported: " ^
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
       } in
       let e' = of_push ob e in
       let (_, body_ast) = lift_tm e' body in
       PPI.Stream, Ast.AMu rng nm sty body_ast
     | _ ->
       T.fail "Pipit.Source.Ast.OfFStar: rec' applied to non-lambda")
  | _ ->
    T.fail "Pipit.Source.Ast.OfFStar: rec' expects exactly one explicit argument"

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
       T.fail "Pipit.Source.Ast.OfFStar: fby init must be a static value")
  | _ ->
    T.fail "Pipit.Source.Ast.OfFStar: fby expects two explicit arguments"

and lift_app_check (e: of_env) (rng: R.range) (args: list T.argv): T.Tac (PPI.mode & Ast.ast) =
  match args with
  | [(prop_tm, _)] ->
    let (_, prop_ast) = lift_tm e prop_tm in
    PPI.Stream, Ast.ACheck rng None prop_ast
  | _ ->
    T.fail "Pipit.Source.Ast.OfFStar: check expects exactly one explicit argument"

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
     T.fail "Pipit.Source.Ast.OfFStar: irrefutable match on non-stream scrutinee is not yet supported");
  let scrut_ty: Ast.sty = T.tc e.oe_tac_env scrut in
  let (e_after, pipit_pat) = pat_of_fstar e pat scrut_ty in
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
      T.fail ("Pipit.Source.Ast.OfFStar: only if-then-else (bool match with True/False arms) is supported in v0; general pattern matches are not yet implemented")
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
    let prim = of_prim_fv_applied e fv implicits in
    let (rm, am) = app_mode_of margs in
    rm, Ast.APrim rng am prim arg_asts

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
   the explicit stream params as `of_binder`s (innermost first,
   matching `Pipit.Source.Ast.Lower.lower_env`), the inferred return
   type of the body (typed against the env that contains the
   pass-through + explicit binders, so any `Tv_Var` references use the
   uniqs from `lb_def` — NOT `lb_typ` — and remain resolvable when
   wrapped back up by the caller), and the lifted AST body. *)
let lift_top_body (tac_env: T.env) (lifted: list (Ast.fqn & PPI.mode)) (body: T.term)
  : T.Tac (list T.binder & list of_binder & T.term & Ast.ast)
=
  let (bs, body) = T.collect_abs body in
  let e0: of_env = { oe_tac_env = tac_env; oe_binders = []; oe_lifted = lifted } in
  let push_param (acc: of_env & list T.binder) (b: T.binder): T.Tac (of_env & list T.binder) =
    let (e, passthrough_rev) = acc in
    if Ref.Q_Explicit? b.qual then
      let nm = of_name_of_namedv (T.binder_to_namedv b) in
      let ob: of_binder = {
        ob_uniq = b.uniq;
        ob_name = nm;
        ob_sty  = strip_refinements b.sort;
        ob_mode = PPI.Stream;
      } in
      (of_push ob e, passthrough_rev)
    else
      (* Pass-through (type / instance / proof) binder. Push into the
         tac env only — no AST binder, no de Bruijn slot. *)
      let nv = T.binder_to_namedv b in
      let e' = { e with oe_tac_env = Ref.push_namedv e.oe_tac_env (Ref.pack_namedv nv) } in
      (e', b :: passthrough_rev)
  in
  let (e_final, passthrough_rev) = T.fold_left push_param (e0, []) bs in
  let ret_ty: T.term = strip_refinements (T.tc e_final.oe_tac_env body) in
  let (_, ast) = lift_tm e_final body in
  (L.rev passthrough_rev, e_final.oe_binders, ret_ty, ast)
