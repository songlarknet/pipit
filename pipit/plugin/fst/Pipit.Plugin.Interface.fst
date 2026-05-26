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

(* Modifier for a `proof_*` attribute: the synthesised proof obligation is
  expected to *fail*. The synthesised `__check_<id>` is tagged with
  `[@@expect_failure]`, so the module typechecks only when the proof
  method fails to discharge the source's `check`s. Useful for confirming
  that a property is genuinely not provable by the chosen method.
  Usage: `[@@proof_induct1; proof_expect_failure]`. *)
irreducible
let proof_expect_failure = ()

(* Attribute on a type definition: ask the preprocessor to splice a
  `has_stream <T>` instance for the type. Currently supports single-
  constructor inductives (records and data classes). Multi-constructor
  types should keep using `derive_has_stream_with_default` explicitly. *)
irreducible
let derive_has_stream = ()

