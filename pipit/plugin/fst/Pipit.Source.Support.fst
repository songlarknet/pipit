module Pipit.Source.Support

[@@plugin]
type mode = | Stream | Static | ModeFun: mode -> explicit: bool -> mode -> mode

assume val rec' (#a: Type) (f: a -> a): a


(* For generated bindings; pointer back to original *)
irreducible
let core_of_source (nm: string) = ()

irreducible
let extract = ()

irreducible
let source_mode (m: mode) = ()

module Tac = FStar.Tactics

[@@plugin]
let lift_tac (nm_src nm_core: string) (m: mode) : Tac.Tac (list Tac.sigelt) =
  []