# `Pipit.Exp.Base` — design notes

Shadow commentary for [Pipit.Exp.Base.fst](Pipit.Exp.Base.fst). The source file
holds the definitions only; the rationale lives here.

## Overview

The core splits into a pure term language (`pterm`), a concrete type language
(`typ`), and a *stratified* stream/tuple term language (`sterm` / `tterm`)
layered on top. This mirrors Pulse's `st_term : F*.term` split — but where Pulse
reuses *full* F\* terms for its pure fragment (it lives inside F\*), `pterm` is a
restricted first-order subset with structural equality, so we get our own small
decidable checker, CSE, and native extraction.

### Why the `table` design went away

The earlier design parameterised `exp t` by a
`table { ty: eqtype; ty_sem: ty -> eqtype; prim: eqtype }`, bundling the value
universe, its F\* denotation, and the primitive set into one global, abstract
record. Three problems drove the change:

1. **Abstract table fields don't extract.** `ty` / `prim` are erased types, so
   `exp` extracted to OCaml with `Obj.t` payloads and any *concrete* prim match
   (a rewrite rule like `sofar_and`) failed to typecheck. Making the
   representation *syntactic* makes the whole thing a plain first-order inductive:
   an eqtype (CSE for free) that extracts to honest OCaml.
2. **A table is global and fixed, but "meta" parameters are local.** E.g. the
   `k` in `running_fold z k b = mu a. k (z fby a) b` is a locally introduced
   primitive whose signature is known in a node body but whose semantics arrive
   at the instantiation site. Environments extend under binders; a table cannot.
   So primitives live in an *environment* passed explicitly to whoever needs
   them.
3. **Different consumers need different slices.** Transforms need nothing (pure
   syntax → syntax); the checker needs only *signatures* (`sigenv`); evaluation
   needs the dynamic interpretation. The table forced everyone to carry all
   three.

## Value types (`typ`)

A *concrete* inductive, not an uninterpreted subset of `pterm` plus a kinding
judgment. The value types the existing pipit examples actually carry are
`int` / `bool` and fixed-width bitvectors — all directly enumerable — so `typ`
just lists them, well-formedness is essentially by construction, and there is no
kinding pass.

Deliberately excluded from v0:

- `unit`: in pipit 1 it is only the result of `check`-only property bodies
  (`bibo2 : stream int -> stream unit`), a placeholder for "no data". Streams
  carry pure values and `check` is not modelled yet, so there is nothing for it
  to type.
- tuples: in the examples these are purely the multi-input / multi-output *node
  calling convention*, already list-shaped at the node layer (`SPureApp` /
  `TStreamApp` argument lists, node/`TRec` results), not genuine value types.
- records / structs: v1, via a `TRecord` former plus a typedef environment.

Also deferred to v1: nominal enums / named typedefs (a `TNamed string` former
plus a typedef environment) and refinement / subrange integers (ttcan's
`S32R.t {min; max}`); v0 treats those as `TInt`. `TBV n` is a fixed-width
bitvector (ttcan `U64 = TBV 64`); a bitvector constant is the literal `LBV n v`.

## Pure terms (`pterm`)

Purely the *value* / primitive-head language. First-order: no binders,
structural equality.

- `PVar name` — a *reference*: a primitive / meta-function operator name, or a
  bound meta parameter, resolved against the environment / binder scope. Appears
  as a `PApp` / `SPureApp` head.
- `PLit l` — a literal. `lit` is a closed sum (keeps every term an eqtype):
  `LBool` / `LInt`, and `LBV w v` a *width-first* bitvector constant of type
  `TBV w` (e.g. `LBV 8 255` = `255'u8`).
- `PCon c args` — a *value constructor application*: irreducible data, e.g. an
  enum tag `PCon "Mode_Running" []` or a bitvector value. Head is a *name*.
- `PApp h args` — a *reducible application*: applying a primitive / meta-function
  (`h` usually a `PVar`) that "might reduce", or a parameterised operator head
  like `bv_get 32`. Distinct from `PCon` so a pass can tell "done" (con) from
  "redex" (app).

Structured *value* literals (record / tuple values) are deferred to v1 with
their types.

## Signatures and environment

- `funty { args; result }` — a primitive / meta-function signature. Kept *out* of
  `typ` (no first-class arrow type): the object language is first-order, so
  arrows appear only in signatures, never as the type of a stream.
- `binder` — a node parameter: `BConst t` (a compile-time-constant value) or
  `BStream t` (a temporal input stream). Higher-order *meta-function* binders
  (the `k` in `running_fold`) are a later `BMeta` case, so first-order
  multi-in/out nodes work now but `running_fold`-proper waits.
- `nodety { params; results }` — a node signature. Unlike `funty`, `results` is a
  *list* of types, because a node is multi-output; it matches a node body's
  `tterm` width.
- `sigenv { prims; nodes }` — the slice the checker consults: signatures only, no
  dynamic semantics. The tables are first-order *association lists* (`L.assoc
  name`), not functions, because a function-typed field cannot be *embedded*
  across the interpreter/native boundary — that would block using the extracted
  `[@@plugin]` definitions (the checker, `to_anf`) as native normalizer steps.
  Assoc lists keep `sigenv` a plain eqtype; environment extension is a cons.

## Stream / tuple terms

Extrinsic: `sterm` carries no F\*-level type indices; well-typedness is the
separate `infer` pass. Everything is an eqtype (built from eqtypes), so CSE and
transforms compare subterms with `=`.

`sterm` — single streams (the analogue of Pulse's `st_term`):

- `SPure p` — a pure/constant stream (a `pterm` value held constant over time).
- `SVar x` — a free (named) stream variable; source-layer only, eliminated by
  `close`.
- `SBVar i` — a bound (de Bruijn) stream variable, referring to a `TRec` / `TLet`
  / parameter binder (all binders are tuple-level).
- `SFby v e` — `v` first, then the previous value of `e`. Single-flow: a tuple
  `fby` flattens to per-component `SFby`s.
- `SPureApp h args` — apply a single-output pointwise primitive / operator `h`
  (a `pterm`: `PVar "and"`, or `PApp (PVar "bv_get") [PLit (LInt 32)]`), resolved
  via `env.prims`.

`tterm` — tuples of streams: a genuine second syntactic category layered *on top
of* `sterm`. An `sterm` never mentions a `tterm`, so the two are *stratified*,
not mutually recursive. A `tterm` denotes a *tuple* of streams (never a stream of
tuples), and all object-stream *binding* lives here, uniformly n-ary. There is no
`tterm → sterm` eliminator former: a single component is read back with the
**projection idiom** `TLet tys tt (TTuple [SBVar i])` (bind the whole tuple,
return component `i`). The source layer applies the dual **meta-unwrap** — a
plain `TTuple [e]` is already the single `sterm` `e` — so ordinary pointwise
expressions stay flat and only genuine tuples (node outputs) pay a `TLet`.

- `TTuple es` — an explicit tuple built from `n` single streams.
- `TStreamApp nm args` — instantiate a (multi-output) node named by a plain
  `string` (resolved via `env.nodes`); denotes the node's result tuple. Unlike
  `SPureApp`, the head is a bare name, not a `pterm`: a node's static parameters
  are `BConst` arguments, not an inline partial application.
- `TRec tys body` — `rec (x_0 .. x_{n-1} : tys). body`: n-ary *mutual* stream
  recursion (Vélus / roadmap `XRec`), the *sole* recursion primitive. `tys` gives
  the arity and member types; `body` is a `tterm` of width `|tys|` in scope of
  all n binders (`SBVar k`, `k < n`, is member `k`). Single-stream feedback
  `mu (x: a). e` is the n = 1 case `TRec [a] (TTuple [e])`.
- `TLet tys rhs bod` — `let (x_0 .. x_{n-1} : tys) = rhs in bod`: bind the `|tys|`
  component streams of the tuple `rhs`, in scope over `bod` only. The sole `let`;
  a single-stream let is the n = 1 case.

## Locally-nameless open / close

These are the only operations that introduce or eliminate free `SVar`s, and they
are intended for the source layer: it builds open bodies with fresh named vars,
then `close`s them into `TLet` / `TRec` binders so the core receives a closed
term. `pterm`s have no binders, so open/close never descend into them; `SPureApp`
/ `TStreamApp` arguments sit at the same binder depth as the application.
`close_rec_s` (on an `sterm`) needs no `tterm` case — an `sterm` never mentions a
`tterm` — and `close_rec_t` layers on top of it. Binders are tuple-level: `TRec`
and the `TLet` *body* shift depth by `|tys|` (the n binders at once); a `TLet`
*rhs* stays at depth `k`, since bindings scope over the body only.

## Type checking

Unlike the old inductive `typing` judgment, checking is a *decidable function*:
with an n-ary `SPureApp` and a signature environment, "type check" is literally
"look up the head's signature and check the arguments". It consults only `sigenv`
(signatures, no dynamic semantics). An inductive presentation can be layered on
later where refinement premises or tactic-driven derivation search are wanted.

- `lit_ty` / `infer_val` — `infer_val` is a first cut: literals only; structured
  constants (records / tuples / constructor applications) are deferred.
- `head_name` — the primitive being applied; `bv_get 32` resolves to `"bv_get"`.
- `infer_s` / `check_args` / `check_node_args` — single-stream inference, giving
  one `typ` and never consulting a `tterm`. `check_node_args`: a `BStream t`
  accepts any stream of type `t`; a `BConst t` accepts only a *constant* stream
  (`SPure`) of type `t`.
- `infer_t` / `infer_args` — tuple inference, giving the *list* of component types
  a `tterm` denotes. `TRec` / `TLet` check the body in the context *extended by
  the n binders* (`tys @ ctx`).
- `well_typed env ctx e a = infer_s env ctx e == Some a`.

## Still to land

- `BMeta` meta-function binders (`running_fold`).
- the soundness relation `stream_eq` relative to an interpretation.
- ANF lowering of recursion: `TRec` type-checks and `close` / `open` handle it,
  but `to_anf` still returns `None` on it — faithful recursive ANF wants the
  register / transition-system view.
