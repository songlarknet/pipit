(* Regression test: polymorphic typeclass instances over user-defined
   type constructors (e.g. `t a = option a`).

   `Pipit.Plugin.Lift.resolve_inst` synthesizes `has_stream (T a)`
   from a poly instance `instance ... {| has_stream a |}: has_stream (T a)`
   plus a pass-through `has_stream a`, by:
     - discovering tcinstance fvs via `Ref.lookup_attr`,
     - matching the candidate by return-type head + arity,
     - building a substitution from candidate return-pattern positions
       to caller `target_args`, and
     - per candidate binder, either passing the substituted sty
       (type-param case) or recursively resolving the instance
       (has_stream sort case).

   Real-world callsite: `Network.TTCan.Prim.Clocked.current_or_else`. *)
module Plugin.Test.Bug.PolyInstance

module PPI  = Pipit.Plugin.Interface
module PPL  = Pipit.Plugin.Lift
module PSSB = Pipit.Prim.HasStream
open Pipit.Plugin.Interface
open Pipit.Source

type t (a: eqtype) = option a

instance has_stream_t (a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (t a) = {
  ty_id = `%t :: (PSSB.ty_id #a);
  val_default = None;
}

let get_value (#a: eqtype) {| PSSB.has_stream a |} (v: t a): a =
  match v with
  | Some v -> v
  | None -> PSSB.val_default

let get_or_else (#a: eqtype) (dflt: a) (clck: t a): a =
  match clck with
  | Some v -> v
  | None -> dflt

(* Polymorphic `current_or_else` over `t a`. The splice's `inst_for`
   synthesizes `has_stream (t a)` from `has_stream_t` plus the
   in-scope `has_stream a` binder. *)
[@@source_mode
  (ModeFun Static false
    (ModeFun Static false
      (ModeFun Static true
        (ModeFun Stream true Stream))))]
let current_or_else (#a: eqtype) {| PSSB.has_stream a |}
  (dflt: a) (clck: t a): a =
  rec' (fun acc ->
    get_or_else (dflt `fby` acc) clck)

%splice[] (PPL.lift_ast_tac1 "current_or_else")

(* ------------------------------------------------------------------ *
 * Regression: a monomorphic call site of a function taking a [t int]
 * argument inside a [rec'] body used to fail with a printer-identical
 * [shallow (t int) / shallow int] subtyping mismatch. The fix lives in
 * [Pipit.Plugin.Lift.resolve_inst]: when the queried [sty] is closed
 * over ground FVars (no local type-binder var from [inst_map]), return
 * [None] and let F* tcresolve the [has_stream sty] query as one unit,
 * so both callsites emit the same closed dictionary term.
 * ------------------------------------------------------------------ *)
let goe_int (dflt: int) (clck: t int): int = get_or_else dflt clck

let add_int (a b: int): int = a + b

(* Baseline: no [t a] arg in the [rec'] body. *)
[@@source_mode (ModeFun Stream true Stream)]
let probe_rec_no_t (a: int): int =
  rec' (fun x -> add_int a (0 `fby` x))

%splice[] (PPL.lift_ast_tac1 "probe_rec_no_t")

(* Regression case: the call passes a [stream (t int)] arg through. *)
[@@source_mode (ModeFun Stream true Stream)]
let probe_rec_with_t (c: t int): int =
  rec' (fun x -> goe_int (0 `fby` x) c)

%splice[] (PPL.lift_ast_tac1 "probe_rec_with_t")
