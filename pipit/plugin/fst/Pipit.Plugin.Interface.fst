(* Interface used by the plugin.
  Most of the contents here shouldn't need to be exposed to users. *)
module Pipit.Plugin.Interface

(*** Types ***)

(* Modes describe computations as streaming or static (non-streaming). *)
[@@plugin]
type mode = | Stream | Static | ModeFun: mode -> explicit: bool -> mode -> mode

(*** Stubs for preprocessing ***)

(* Recursive streams are written to use this combinator *)
assume val rec' (#a: Type) (f: a -> a): a

(*** Attributes ***)

(* Annotate a core function with a pointer back to its source. *)
irreducible
let core_of_source (nm: string) (m: mode) = ()

(* Annotate a source function with its mode.
 The lift tactic uses this to figure out which arguments need to be streams.  *)
irreducible
let source_mode (m: mode) = ()

(* Mark a core function as being lifted.
  Functions annotated with this should also be annotated with core_of_source.
  This annotation makes it easier for the implementation to search for all core functions.
  *)
irreducible
let core_lifted = ()
(* TODO merge into core_lifted?? *)
irreducible
let core_lifted_prim = ()

(* Mark a source function as one whose `check`s should be discharged
  automatically by 1-induction. The preprocessor synthesises a
  `__check_<id>` binding that asserts `induct1 (system_of_exp __core_<id>)`
  by normalisation and then blesses the core expression. The shape is
  arity-polymorphic, so it works for any number of stream arguments. *)
irreducible
let proof_induct1 = ()

(* Negative-test variant of `proof_induct1`. Synthesises the same
  `__check_<id>` binding but tags it with `[@@expect_failure]`, so the
  module typechecks only when 1-induction fails to discharge the source's
  `check`s. Useful for confirming that the synthesised check actually
  rejects bogus properties. *)
irreducible
let proof_induct1_expect_failure = ()

