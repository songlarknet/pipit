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
