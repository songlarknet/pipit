(* Pipit source AST.

  An untyped intermediate representation sitting between F*'s `TermView`
  and Pipit's core `exp`. Produced by the lift pass (`Pipit.Plugin.Lift`)
  and consumed by the lower pass (`Pipit.Source.Ast.Lower`), which builds
  a checked core expression over `Pipit.Prim.Shallow.table`.

  Design notes:
  * Untyped: the AST itself carries no F*-level type indices. Types of
    subexpressions are recovered by `Lower`; binders carry an `sty` tag
    so that the lowering pass can rebuild the typing context.
  * Names, not de Bruijn. `Lower` converts to de Bruijn while building
    the core expression. Names are friendlier for the lift pass to emit
    and easier to debug.
  * Opaque payloads (literal values, F* types, primitive functions) are
    carried as quoted `FStar.Tactics.V2.term`s. This keeps the AST cheap
    to construct from the lift pass and defers concrete resolution until
    lowering.
  * Every node carries a `range` so that `Lower` can report errors at the
    original source location.

  Deliberately not included in v0:
  * `AMatch` (multi-arm): lift handles only the if-then-else shape (a
    `Tv_Match` on a bool scrutinee with `True`/`False` arms) by emitting
    an `APrim` over `PipitRuntime.Prim.p'select`. Multi-arm pattern
    matches on data-constructor scrutinees are not supported. Even an
    eventual implementation likely needs to introduce clocking /
    activation so that the substreams under a non-matching arm do not
    advance their state; the legacy lift's eager-evaluate-all-branches
    \"select\" semantics is semantically dubious and we do not want to
    bake it in here. Single-arm irrefutable matches (tuple / record /
    single-ctor destructure) ARE supported via `ALetMatch`.
  * `AContract`: revived in a follow-up with `Pipit.Sugar.Contract`.
  * `ALemma`: revived alongside the ttcan port.
  * First-class abstractions: callers are reified to top-level bindings.
*)
module Pipit.Source.Ast

module T   = FStar.Tactics.V2
module PPI = Pipit.Plugin.Interface

open FStar.Range

(*** Names and labels ***)

(* A local (unqualified) name, e.g. a let-bound variable or function
   parameter. *)
type name  = string

(* A fully-qualified path, matching the representation returned by
   `FStar.Tactics.V2.inspect_fv` and accepted by `pack_fv`. Used for
   references to top-level lifted bindings. *)
type fqn   = list string

type label = string

(*** Application modes ***)

(* How a primitive application is invoked. Tells `Lower` which smart
   constructor (or none at all) to wrap the application in.

   * `AppPureConst` — all arguments are static values, the result is a
     static value. Lowers to a direct F* application; no Pipit
     wrapping. Useful for evaluating constant subexpressions of an
     otherwise streaming program.
   * `AppPureStream` — a pure F* function lifted over streams. Some or
     all arguments are streams, and the result is a stream. Lowers via
     `XApps (XApp ... (XApp (XPrim p) a1) ... an)`.

   Only `APrim` carries an `app_mode`. `ACallStream` is always a stream
   call, by construction. *)
type app_mode =
  | AppPureConst
  | AppPureStream

(*** Modes ***)

(* The mode of a value or binder. Reuses the plugin interface's `mode`
   so the OCaml preprocessor and the F* tactic agree on representation. *)
type mode = PPI.mode

(*** Types and literals (opaque payloads) ***)

(* A source-level type, carried as a quoted F* type term. `Lower` turns
   this into the corresponding `Pipit.Prim.Shallow.shallow_type`. *)
type sty = T.term

(* A literal value: its F* type and the quoted F* value. *)
noeq
type lit = {
  lit_ty: sty;
  lit_tm: T.term;
}

(* A primitive: the F* function plus the per-argument and result source
   types of its application form. Mirrors the contents of
   `Pipit.Prim.Shallow.prim`. The (`prim_arg_tys`, `prim_ret_ty`) pair
   is what `Lower` builds the `funty` from; the full F* function type
   is recoverable as `prim_arg_tys -> ... -> prim_ret_ty`. *)
noeq
type prim = {
  prim_id:      option name;
  prim_arg_tys: list sty;
  prim_ret_ty:  sty;
  prim_fn:      T.term;
}

(* A reference to another lifted source binding that has a core
   definition (i.e. another `#lang-pipit` binding). The `br_mode` is
   the full functional mode of the binding (e.g. `ModeFun Static true
   (ModeFun Stream true Stream)`), so callers know which arguments to
   pass as static values vs. streams. `br_arg_tys` carries the source
   parameter types in source-text order (outermost lambda first); the
   lower pass uses them to build the `XLet`/`weaken` chain that
   substitutes call-site arguments into the callee's `__core_*`
   expression. The return type is recoverable from the callee's
   signature but is not needed by `Lower` since the spliced sigelt
   gets its `lb_typ` from the surrounding context.

   `br_implicits` are the call-site implicit/instance arguments that
   F* resolved when typechecking the user-facing call (e.g. `#int`,
   `#bool`, `#has_stream_int`, `#has_stream_bool` for `fst (x, y)`
   on `stream int * stream bool`). They are pre-applied to the callee
   `__core_*` reference by `Lower` so polymorphic callees become
   monomorphic at each call site; if the callee is ground, this list
   is empty. *)
noeq
type binding_ref = {
  br_fqn:        fqn;
  br_mode:       mode;
  br_arg_tys:    list sty;
  br_implicits:  list T.argv;
}

(*** Patterns ***)

(* An irrefutable structural pattern used by `ALetMatch` (single-arm
   destructure of a tuple / record / single-ctor data value). The
   walker in `Pipit.Source.Ast.OfFStar` only emits these for patterns
   that bind variables (or wildcards) under any sequence of nested
   data constructors. Multi-arm matching is not represented yet.

   * `PWild` — `_`. Does not introduce a binder. Also used for the
     implicit/dot subpatterns that get elided.
   * `PVar name sty mode` — bind `name` of type `sty` in mode `mode`
     to the corresponding sub-value. `sty` is the source type of the
     binder; `mode` is the binder's value mode (today always `Stream`
     for irrefutable destructure of a stream scrutinee).
   * `PCon ctor subs` — match a data constructor by its FQN and
     destructure its explicit fields, in declaration order. The
     `Lower` pass uses `ctor` to compute each field's projector
     (`__proj__<Ctor>__item__<field>`). *)
noeq
type pat =
  | PWild  : pat
  | PVar   : name -> sty -> mode -> pat
  | PCon   : fqn -> list pat -> pat

(*** AST ***)

noeq
type ast =
  (* `v` — literal lifted into a constant stream. *)
  | ALit   : range -> lit -> ast
  (* `x` — reference to a binder introduced by ALet/AMu/ALetrec or a
     parameter of the enclosing source function. The `mode` is carried
     so consumers don't need to chase the binder site to learn whether
     `x` is a stream or a static value. *)
  | AVar   : range -> name -> mode -> ast
  (* `p e1 ... en` — application of a pure F* function `p`. The
     `app_mode` records whether this is an all-static application
     (`AppPureConst`, lowers to a plain F* call) or a stream lifting
     (`AppPureStream`, lowers via `XApps`/`XApp`/`XPrim`). *)
  | APrim  : range -> app_mode -> prim -> list ast -> ast
  (* `f e1 ... en` — call to another lifted source binding that has a
     core definition (i.e. another `#lang-pipit` binding). Always
     stream-mode by construction; no `app_mode`. *)
  | ACallStream : range -> binding_ref -> list ast -> ast
  (* `v `fby` e` — initial value followed by a stream. *)
  | AFby   : range -> lit -> ast -> ast
  (* `let x: sty = def in body`, with `mode` describing whether `x` is a
     stream or static binding. *)
  | ALet   : range -> name -> mode -> sty -> ast -> ast -> ast
  (* `match scrut with | pat -> body` for a single irrefutable arm
     (tuple / record / single-ctor destructure). The `sty` is the
     scrutinee's source type, which `Lower` needs to recover the
     constructor's implicit type arguments when emitting projector
     applications. The pattern is walked at lower time; each `PVar`
     leaf introduces a stream binder bound to a projector application
     on the scrutinee.

     Refutable / multi-arm matches are not represented here; the
     bool/if-then-else shape goes through `APrim AppPureStream` over
     `PipitRuntime.Prim.p'select` instead. *)
  | ALetMatch : range -> pat -> sty -> ast -> ast -> ast
  (* `rec' (fun (x: sty) -> body)` — recursive stream definition.
     Mirrors `XMu` in the core expression. *)
  | AMu     : range -> name -> sty -> ast -> ast
  (* `let rec x1: sty1 = b1 and ... and xn: styn = bn in cont` —
     mutual recursion. All bindings are in scope in every `bi` and in
     `cont`. *)
  | ALetrec : range -> list (name & sty & ast) -> ast -> ast
  (* `check ?label e` — proof obligation to be discharged at the core
     level. *)
  | ACheck : range -> option label -> ast -> ast
