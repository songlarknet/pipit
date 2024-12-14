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

(*** Public Attributes -- these should be moved to the public interface ***)
(* Mark to be extracted *)
// irreducible
// let extract = ()
// irreducible
// let defer_check = ()
