(* Core term representation for pipit2: a shared *pure* term language and a
   *stream* (temporal) term language layered on top.

   This replaces the earlier `table`-parameterised design. Previously `exp t`
   was parameterised by a `table { ty: eqtype; ty_sem: ty -> eqtype; prim:
   eqtype }`, bundling the value universe, its F* denotation, and the primitive
   set into one global, abstract record. Three problems drove the change:

     1. Abstract table fields do not extract. `ty`/`prim` are erased types, so
        `exp` extracted to OCaml with `Obj.t` payloads and any *concrete* prim
        match (a rewrite rule like `sofar_and`) failed to typecheck. Making the
        representation *syntactic* makes the whole thing a plain first-order
        inductive: an eqtype (CSE for free) that extracts to honest OCaml.

     2. A table is *global and fixed*, but higher-order "meta" parameters --
        e.g. the `k` in `running_fold z k b = mu a. k (z fby a) b` -- are
        *locally* introduced primitives whose signature is known in a node body
        but whose semantics arrive at the instantiation site. Environments
        extend under binders; a table cannot. So primitives live in an
        *environment* passed explicitly to whoever needs them.

     3. Different consumers need different slices of that environment: transforms
        need nothing (pure syntax -> syntax); the checker needs only *signatures*
        (a type environment, `sigenv` below); evaluation needs the dynamic
        interpretation. The table forced everyone to carry all three.

   Structure (mirrors Pulse's split `st_term : F*.term`): a `pterm` (pure term:
   value literals and primitive/constructor heads and structured data), a `typ`
   (a small *concrete* type language), and an `sterm` (stream term: the temporal
   fragment with `fby`/`mu`) built on top. Unlike Pulse -- which reuses *full* F*
   terms for its pure fragment because it is inside F* -- `pterm` is a restricted
   first-order subset with structural equality, so we get our own small decidable
   checker, CSE, and native extraction.

   Types are a *concrete* inductive (`typ`), not an uninterpreted subset of
   `pterm`. An earlier draft made types just `pterm`s read in type position and
   layered a kinding judgment on top to carve out the well-formed ones (a type
   never contained `PApp`, a bitvector width was a `PLit` accepted at a `KNat`
   kind, ...). For pipit2 v0 that is more machinery than the object language
   needs: the value types the existing pipit examples actually carry are `int` /
   `bool` and fixed-width bitvectors, all directly enumerable. So `typ` lists
   them, well-formedness is (almost) by construction, and the kinding pass is
   gone. (`unit` -- only a `check`-body placeholder -- tuples -- the multi-in/out
   node calling convention -- and records are all deliberately excluded; see
   `typ`. Nominal enums / named typedefs and structs / nominal records, used by
   the ttcan example, are the first things a v1 would add, via `TNamed` /
   `TRecord` formers and a typedef environment.)

   `pterm` is thus purely the *value* / primitive-head language: literals,
   value constructors (an enum tag, a bitvector value), and the primitive /
   operator heads (a `pterm`) that `SPureApp` applies. The term language is
   *stratified* into single streams (`sterm`) and tuples of streams (`tterm`):
   `SPureApp` (an `sterm`) applies a single-output pointwise primitive / operator
   (head a `pterm`, `env.prims`); `TStreamApp` (a `tterm`) instantiates a
   multi-output node *by name* (head a plain `string`, `env.nodes`) and denotes a
   *tuple* of streams, with a single component read back by the projection idiom
   `TLet tys tt (TTuple [SBVar i])` (there is no `SProject` former: an `sterm`
   never mentions a `tterm`, so the two sorts are *stratified*, not mutually
   recursive).

   Locally nameless, as before, but only for *object stream* binders: binding is
   uniformly n-ary and lives at the *tuple* level -- `TRec` and `TLet` each bind
   `|tys|` `SBVar`s at once (as do node parameters) -- and `close` / `open`
   convert to/from free `SVar`s in the source layer, so the core operates on
   closed terms. There are no binders inside `pterm` or `typ`, and meta binders
   (type variables, meta-functions) are *named* and live at the node level (not
   yet in this module), so the only bound variables are object streams.

   The node layer lands incrementally. Node parameters are `binder`s -- a
   *const* value (`BConst`) or a *stream* (`BStream`); higher-order meta-function
   binders (the `k` in `running_fold`) are a later `BMeta` case, so first-order
   multi-in/multi-out nodes work now but `running_fold`-proper waits. A node is
   multi-output: `nodety.results` is a *list* of types, matching a node body's
   `tterm` (a *tuple* of streams). The tuple sort `tterm` is a genuine second
   syntactic category (not a value `typ`): a `tterm` is built by `TTuple` /
   `TStreamApp` / `TRec` / `TLet` and consumed by the projection idiom
   `TLet tys tt (TTuple [SBVar i])`. The shallow source layer represents a stream
   *as* a (width-1) `tterm` and meta-unwraps a plain `TTuple [e]` back to the
   `sterm` `e`, so ordinary pointwise expressions stay flat; multi-output node
   calls are the one case that pays a real `TLet`, which a later CSE / sharing-
   recovery pass and a core ANF language normalize.

   Still to land: `BMeta` meta-function binders (`running_fold`), the soundness
   relation `stream_eq` relative to an interpretation, and the ANF lowering of
   recursion (`TRec` type-checks and `close`/`open` handle it, but `to_anf`
   still returns `None` on it -- faithful recursive ANF wants the register /
   transition-system view). *)
module Pipit.Exp.Base

module L = FStar.List.Tot

(* ----- Pure terms ------------------------------------------------------- *)

(* Object-level literals. A closed sum keeps every term an eqtype and extraction
   free of `Obj.t`. Bitvector *constants* will be an `LInt` value read at a
   `bv w` type, not a separate literal kind. *)
[@@plugin]type lit =
  | LBool : bool -> lit
  | LInt  : int  -> lit

(* Pure terms: the *value* / primitive-head language -- value literals,
   value constructors, structured data, and the primitive / operator heads
   that `SPureApp` applies (a node instance names its node with a plain
   `string`, not a `pterm`). Types are a *separate* concrete inductive (`typ`,
   below), not a subset of this. First-order: no binders, structural equality.

     - `PVar name`  : a *reference* -- a primitive or meta-function operator
                      name, or a bound meta parameter, resolved against the
                      environment / binder scope. Appears as a `PApp` /
                      `SPureApp` / `SStreamApp`
                      head.
     - `PLit l`     : a literal.
     - `PCon c args`: a *value constructor application* -- irreducible data, e.g.
                      an enum tag `PCon "Mode_Running" []` or a bitvector value.
                      The head is a *name*, never a term.
     - `PApp h args`: a *reducible application* -- applying a primitive /
                      meta-function (`h` is usually a `PVar`) that "might
                      reduce", or a parameterised operator head like `bv_get 32`
                      used as an `SPureApp` / `SStreamApp` head. Distinct from `PCon` so a pass can
                      tell "done" (con) from "redex" (app).

   Structured *values* (record / tuple literals) are deferred to v1 along with
   their types; see `typ`. *)
[@@plugin]
type pterm =
  | PVar    : string -> pterm
  | PLit    : lit -> pterm
  | PCon    : string -> list pterm -> pterm
  | PApp    : pterm -> list pterm -> pterm

(* Value types: a small *concrete* type language for the value a stream carries.
   Enumerable, so well-formedness is essentially by construction and there is no
   kinding pass. First-order (no arrow type: the object language is first-order,
   arrows appear only in `funty` signatures), an eqtype (structural equality
   drives CSE and the checker).

   Deliberately *not* here:

     - `unit`: in pipit 1 it is only the result of `check`-only property bodies
       (`bibo2 : stream int -> stream unit`), a placeholder for "no data". Since
       streams carry pure values and `check` is not modelled yet, there is
       nothing for it to type; it returns with the check node.
     - tuples: in the examples these are purely the multi-input / multi-output
       *node calling convention* (`controller_body : ... -> stream (bool & bool)`
       returning `(sol_en, nok_stuck)`, then `let (estop, level_low) = i`), not
       genuine value types. That plumbing is already list-shaped -- `SPureApp` /
       `SStreamApp`'s `list sterm` arguments, and the future n-ary node / `SRec` results -- so
       it belongs at the node layer, not as a first-class value type.
     - records / structs: the ttcan example carries them, but nominal records
       (a `TRecord` former plus a typedef environment) are a v1 addition; v0
       has no structured value type.

   Deferred to v1: nominal enums / named typedefs (a `TNamed string` former plus
   a typedef environment), structs / nominal records (a `TRecord` former), and
   refinement / subrange integers (ttcan's `S32R.t {min; max}`); v0 treats those
   as `TInt`. *)
[@@plugin]
type typ =
  | TBool   : typ
  | TInt    : typ
  | TBV     : nat -> typ                    (* fixed-width bitvector, e.g. ttcan U64 = TBV 64 *)

(* A primitive / meta-function signature: argument types and a result type. Kept
   *out* of `typ` (no first-class arrow type) because the object language is
   first-order -- arrows appear only in signatures, never as the type of a
   stream. *)
[@@plugin]
type funty = { args: list typ; result: typ }

(* A node parameter (binder). First-order for now: `BConst t` is a compile-time-
   constant value of a simple `typ`; `BStream t` is a temporal input stream.
   Higher-order *meta-function* binders (the `k` in `running_fold`) are a later
   `BMeta` case, so first-order multi-in/multi-out nodes are expressible now but
   `running_fold`-proper waits. *)
[@@plugin]
type binder =
  | BConst  : typ -> binder
  | BStream : typ -> binder

(* A node signature: a list of parameter binders and -- unlike `funty` -- a
   *list* of result types, because a node is multi-output. The results match a
   node body's `tterm` width; a `TStreamApp` denotes that tuple of streams,
   projected with the `TLet` / `SBVar` idiom. The tuple is a syntactic sort
   (`tterm`), not a value `typ`. *)
[@@plugin]
type nodety = { params: list binder; results: list typ }

(* The signature environment the checker consults: `prims` gives primitive /
   operator (single-output) signatures, `nodes` gives node (multi-output)
   signatures. Only *signatures* -- no dynamic semantics -- which is exactly the
   slice type checking needs. With types now concrete there is no type-
   constructor table to carry. A node's meta binders extend the environment
   locally; a fixed instantiation supplies a separate dynamic environment (not
   modelled here).

   The tables are first-order association lists (`L.assoc name`), not functions:
   a function-typed field cannot be *embedded* across the interpreter/native
   boundary, so it would block using the extracted `[@@plugin]` definitions (the
   checker, `to_anf`) as native normalizer steps. Assoc lists keep `sigenv` a
   plain eqtype, consistent with the rest of the representation; environment
   extension is just a cons. *)
[@@plugin]
type sigenv = {
  prims: list (string & funty);
  nodes: list (string & nodety);
}

(* ----- Stream terms ----------------------------------------------------- *)

(* A free (named) object-stream variable, carrying its type. Introduced only in
   the source layer and eliminated by `close`. *)[@@plugin]type svar = { svname: nat; svty: typ }

(* Stream (temporal) terms -- the analogue of Pulse's `st_term`. Extrinsic:
   `sterm` carries no F*-level type indices; well-typedness is the separate
   `infer` pass. An eqtype (built from eqtypes), so CSE and transforms compare
   subterms with `=`. *)
[@@plugin]
type sterm =
  (* a pure/constant stream (a `pterm` value, held constant over time) *)
  | SPure : pterm -> sterm
  (* a free (named) stream variable, source-layer only *)
  | SVar  : svar -> sterm
  (* a bound (de Bruijn) stream variable, referring to a `TRec` / `TLet` /
     parameter binder (all binders are tuple-level) *)
  | SBVar : nat -> sterm
  (* `v fby e`: the constant `v` first, then the previous value of `e`.
     Single-flow: a tuple `fby` flattens to per-component `SFby`s. *)
  | SFby  : pterm -> sterm -> sterm
  (* apply a single-output primitive / operator `head` to stream arguments
     (pointwise). The head is a `pterm` (`PVar "and"`, or `PApp (PVar "bv_get")
     [PLit (LInt 32)]`); `env.prims` resolves it. Single-flow. *)
  | SPureApp : pterm -> list sterm -> sterm

(* Tuple-of-streams terms: the second syntactic category, layered *on top of*
   `sterm` (an `sterm` never mentions a `tterm`, so the two are *stratified*, not
   mutually recursive). A `tterm` denotes a *tuple* of streams (never a stream of
   tuples). All object-stream *binding* lives here, uniformly n-ary. There is no
   `tterm` -> `sterm` eliminator former: a single component is read back with the
   *projection idiom* `TLet tys tt (TTuple [SBVar i])` -- bind the whole tuple,
   return component `i`. The source layer applies the dual *meta*-unwrap (a plain
   `TTuple [e]` is already the single `sterm` `e`) so ordinary pointwise
   expressions stay flat and only genuine tuples (node outputs) pay a `TLet`. *)
[@@plugin]
type tterm =
  (* an explicit tuple built from `n` single streams *)
  | TTuple     : list sterm -> tterm
  (* instantiate a (multi-output) node, named by a plain `string`, on stream
     arguments. Denotes the node's result tuple; `env.nodes` resolves the name.
     (Unlike `SPureApp`, the head is a bare name, not a `pterm`: a node's static
     parameters are `BConst` arguments, not an inline partial application.) *)
  | TStreamApp : string -> list sterm -> tterm
  (* `rec (x_0 .. x_{n-1} : tys). body`: n-ary *mutual* stream recursion (Vélus /
     roadmap `XRec`), the *sole* recursion primitive. `tys` gives the arity and
     member types; `body` is a `tterm` of width `|tys|` in scope of all n binders
     (`SBVar k`, `k < n`, refers to member `k`). Single-stream feedback
     `mu (x: a). e` is the n = 1 case, `TRec [a] (TTuple [e])`. *)
  | TRec       : list typ -> tterm -> tterm
  (* `let (x_0 .. x_{n-1} : tys) = rhs in body`: bind the `|tys|` component
     streams of the tuple `rhs`, in scope over `body` only (`SBVar k` referring
     to component `k`). The sole `let`; a single-stream let is the n = 1 case,
     and the `n`-ary projection idiom above. *)
  | TLet       : list typ -> tterm -> tterm -> tterm

(* ----- Locally-nameless open / close (object binders only) -------------- *)

(* These are the only operations that introduce or eliminate free `SVar`s, and
   they are intended for the source layer: it builds open bodies with fresh
   named vars, then `close`s them into `TLet` / `TRec` binders so the core
   receives a closed term. `pterm`s have no binders, so open/close never descend
   into them; `SPureApp` / `TStreamApp` arguments sit at the same binder depth as
   the application. `close_rec_s` (on an `sterm`) needs no `tterm` case -- an
   `sterm` never mentions a `tterm` -- and `close_rec_t` layers on top of it. *)

let rec close_rec_s (k: nat) (x: svar) (e: sterm): Tot sterm (decreases e) =
  match e with
  | SPure _         -> e
  | SVar y          -> if y = x then SBVar k else e
  | SBVar _         -> e
  | SFby v e'       -> SFby v (close_rec_s k x e')
  | SPureApp h args -> SPureApp h (close_args_s k x args)
and close_args_s (k: nat) (x: svar) (args: list sterm): Tot (list sterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> close_rec_s k x a :: close_args_s k x tl

let rec close_rec_t (k: nat) (x: svar) (t: tterm): Tot tterm (decreases t) =
  match t with
  | TTuple es          -> TTuple (close_args_s k x es)
  | TStreamApp nm args -> TStreamApp nm (close_args_s k x args)
  | TRec tys body      -> TRec tys (close_rec_t (k + L.length tys) x body)
  | TLet tys rhs bod   -> TLet tys (close_rec_t k x rhs) (close_rec_t (k + L.length tys) x bod)

let rec open_rec_s (k: nat) (u: sterm) (e: sterm): Tot sterm (decreases e) =
  match e with
  | SPure _         -> e
  | SVar _          -> e
  | SBVar i         -> if i = k then u else e
  | SFby v e'       -> SFby v (open_rec_s k u e')
  | SPureApp h args -> SPureApp h (open_args_s k u args)
and open_args_s (k: nat) (u: sterm) (args: list sterm): Tot (list sterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> open_rec_s k u a :: open_args_s k u tl

let rec open_rec_t (k: nat) (u: sterm) (t: tterm): Tot tterm (decreases t) =
  match t with
  | TTuple es          -> TTuple (open_args_s k u es)
  | TStreamApp nm args -> TStreamApp nm (open_args_s k u args)
  | TRec tys body      -> TRec tys (open_rec_t (k + L.length tys) u body)
  | TLet tys rhs bod   -> TLet tys (open_rec_t k u rhs) (open_rec_t (k + L.length tys) u bod)

(* Close `x` into a fresh outermost binder (index 0) of a single stream. *)
let close (x: svar) (e: sterm): sterm = close_rec_s 0 x e

(* Open the outermost binder (index 0) with the free variable `x`. *)
let open_var (x: svar) (e: sterm): sterm = open_rec_s 0 (SVar x) e

(* ----- Type checking (decidable, environment-driven) -------------------- *)

(* ----- Type checking (decidable, environment-driven) -------------------- *)

(* Unlike the old inductive `typing` judgment, checking is a decidable function
   here: with an n-ary `SPureApp` and a signature environment, "type check" is
   literally "look up the head's signature and check the arguments". It consults
   only `sigenv` -- signatures, no dynamic semantics -- which is exactly the
   slice type checking needs. (An inductive presentation can be layered on later
   where refinement premises or tactic-driven derivation search are wanted.) *)

(* Base type of a literal. *)
let lit_ty (l: lit): typ =
  match l with
  | LBool _ -> TBool
  | LInt  _ -> TInt

(* Type of a constant pure term. First cut: literals only; structured constants
   (records / tuples / constructor applications) are deferred. *)
let infer_val (v: pterm): option typ =
  match v with
  | PLit l -> Some (lit_ty l)
  | _      -> None

(* Head name of an application: the primitive / meta-function being applied.
   `bv_get 32` (a parameterised prim) resolves to name "bv_get"; its width-
   dependent signature is a later concern. *)
let head_name (h: pterm): option string =
  match h with
  | PVar n          -> Some n
  | PApp (PVar n) _ -> Some n
  | _               -> None

(* Infer the type of a stream term against a context of de Bruijn binder types
   and the signature environment. Returns `None` on ill-typed terms. Split by
   sort: `infer_s` gives a single `typ` and never consults a `tterm`; `infer_t`
   (below) gives a *list* of types (the tuple widths), reading a single component
   back through the projection idiom `TLet tys tt (TTuple [SBVar i])`. *)
let rec infer_s (env: sigenv) (ctx: list typ) (e: sterm): Tot (option typ) (decreases e) =
  match e with
  | SPure v         -> infer_val v
  | SVar x          -> Some x.svty
  | SBVar i         -> if i < L.length ctx then Some (L.index ctx i) else None
  | SFby v e'       -> (match infer_val v with
                       | Some a -> if infer_s env ctx e' = Some a then Some a else None
                       | None   -> None)
  | SPureApp h args -> (match head_name h with
                       | Some n -> (match L.assoc n env.prims with
                                   | Some ft -> if check_args env ctx args ft.args
                                               then Some ft.result else None
                                   | None    -> None)
                       | None   -> None)
and check_args (env: sigenv) (ctx: list typ) (args: list sterm) (tys: list typ)
: Tot bool (decreases args) =
  match args, tys with
  | [], []             -> true
  | a :: atl, t :: ttl -> infer_s env ctx a = Some t && check_args env ctx atl ttl
  | _, _               -> false
(* Check node arguments against parameter binders: a `BStream t` accepts any
   stream of type `t`; a `BConst t` accepts only a *constant* stream (`SPure`)
   of type `t`. *)
and check_node_args (env: sigenv) (ctx: list typ) (args: list sterm) (params: list binder)
: Tot bool (decreases args) =
  match args, params with
  | [], []                     -> true
  | a :: atl, BStream t :: ptl -> infer_s env ctx a = Some t && check_node_args env ctx atl ptl
  | a :: atl, BConst t :: ptl  ->
    (match a with SPure v -> infer_val v = Some t | _ -> false) && check_node_args env ctx atl ptl
  | _, _                       -> false

(* Tuple inference: `infer_t` gives the *list* of component types a `tterm`
   denotes; `infer_args` synthesizes an explicit tuple's component types. Layered
   on `infer_s` (block above), never the reverse. *)
let rec infer_args (env: sigenv) (ctx: list typ) (args: list sterm)
: Tot (option (list typ)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match infer_s env ctx a, infer_args env ctx tl with
               | Some t, Some ts -> Some (t :: ts)
               | _, _            -> None)
and infer_t (env: sigenv) (ctx: list typ) (t: tterm): Tot (option (list typ)) (decreases t) =
  match t with
  (* an explicit tuple: synthesize each component's type. *)
  | TTuple es          -> infer_args env ctx es
  (* a node instantiation: look up the signature, check the arguments against the
     parameter binders, return the node's result types. *)
  | TStreamApp nm args -> (match L.assoc nm env.nodes with
                          | Some nt -> if check_node_args env ctx args nt.params
                                      then Some nt.results else None
                          | None    -> None)
  (* `TRec tys body`: the width-`|tys|` body is checked at the tuple type `tys`
     in the context *extended by the n binders* (`tys @ ctx`). *)
  | TRec tys body      -> if infer_t env (L.append tys ctx) body = Some tys
                         then Some tys else None
  (* `TLet tys rhs bod`: `rhs` must produce the tuple `tys`; `bod` is inferred in
     the context *extended by the n binders*. *)
  | TLet tys rhs bod   -> if infer_t env ctx rhs = Some tys
                         then infer_t env (L.append tys ctx) bod else None

(* `e` is well typed at `a` when inference agrees. *)
let well_typed (env: sigenv) (ctx: list typ) (e: sterm) (a: typ): prop =
  infer_s env ctx e == Some a
