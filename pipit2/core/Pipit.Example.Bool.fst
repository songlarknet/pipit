(* Pipit.Example.Bool -- a concrete boolean signature environment and a first
   rewrite rule.

   This instantiates the syntactic core at a tiny value universe (one type,
   `bool`) with a handful of named primitives (plus one two-output node,
   `ctrl`), and defines `sofar_and` -- the deliberately gentle temporal rewrite
   from the roadmap
   (../doc/roadmap/next-project-plan.md, M1'):

     sofar (a && b)  ~=  (sofar a) && (sofar b)

   Two things replace the old `table`-based version:

     - primitives now live in an *environment* (`benv`), keyed by name and
       carrying only signatures (no dynamic semantics); and

     - the rule `step_sofar_and` matches fully *concrete* syntax (`PVar "sofar"`,
       `[_; _]`), so -- unlike the old table-abstract `prim`, which extracted to
       `Obj.t` and could not be matched in OCaml -- it now extracts to honest
       native OCaml.

   The rule is unverified: its soundness (`stream_eq` between the two sides) is
   deferred to the congruence / rule-lemma machinery. *)
module Pipit.Example.Bool

module PEB = Pipit.Exp.Base

(* One object-level value type: booleans. *)
let bool_ty: PEB.typ = PEB.TBool

(* Primitive heads (pure terms in operator position). `p_sofar` is a unary
   temporal operator ("has held at every instant so far"); the rest are the
   usual boolean connectives. *)
let p_and:   PEB.pterm = PEB.PVar "and"
let p_or:    PEB.pterm = PEB.PVar "or"
let p_not:   PEB.pterm = PEB.PVar "not"
let p_sofar: PEB.pterm = PEB.PVar "sofar"

(* The boolean signature environment: the connectives and the unary temporal
   `sofar` are primitives over `bool`. Carries only signatures -- the checker
   consults nothing else. First-order assoc lists (see `Pipit.Exp.Base.sigenv`):
   `L.assoc name` resolves a head. *)
let benv: PEB.sigenv = {
  PEB.prims = [
    "and",   ({ PEB.args = [bool_ty; bool_ty]; result = bool_ty });
    "or",    ({ PEB.args = [bool_ty; bool_ty]; result = bool_ty });
    "not",   ({ PEB.args = [bool_ty];          result = bool_ty });
    "sofar", ({ PEB.args = [bool_ty];          result = bool_ty });
  ];
  (* a two-input, two-output boolean node (the ex-tuple calling convention) *)
  PEB.nodes = [
    "ctrl", ({ PEB.params  = [PEB.BStream bool_ty; PEB.BStream bool_ty];
               results = [bool_ty; bool_ty] });
  ];
}

(* The rewrite rule, as a local `step`: push `sofar` through `&&`. Identity on
   every other shape, so `Pipit.Transform.Rewrite.rewrite step_sofar_and` fires
   it at every `sofar (_ && _)` in a term, including under binders. *)
let step_sofar_and (e: PEB.sterm): PEB.sterm =
  match e with
  | PEB.SPureApp (PEB.PVar "sofar") [PEB.SPureApp (PEB.PVar "and") [a; b]] ->
    PEB.SPureApp p_and [PEB.SPureApp p_sofar [a]; PEB.SPureApp p_sofar [b]]
  | _ -> e
