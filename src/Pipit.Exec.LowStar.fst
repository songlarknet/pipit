(* Simple, inefficient integration with C. *)
module Pipit.Exec.LowStar

module EE = Pipit.Exec.Exp

module SB = Pipit.System.Base
module SX = Pipit.System.Exec

module B = LowStar.Buffer
module Tac = FStar.Tactics

open LowStar.BufferOps
open FStar.HyperStack.ST

(* Tactic for normalizing pure expressions, such as systems.
  The translation from an expression to a system involves a lot of machinery,
  which we want to get rid of.
  This is probably overkill.
 *)
let tac_normalize_pure () =
  Pipit.Tactics.norm_full ();
  // Tac.dump "tac_normalize_pure";
  Tac.trefl ()


(* Tactic for normalizing extractable imperative expressions. We need to be a
  little bit careful here to avoid unfolding the details of the mutable heap,
  or we might end up with a program that Karamel doesn't understand.
  We unfold the details of Pipit.Context.*, Pipit.Exec.*, Pipit.System.*. We
  also unfold anything the user has marked inline_for_extraction. *)
let tac_extract () =
  Tac.norm [nbe; primops; iota; zeta; delta_namespace ["Pipit"; "FStar.Pervasives"]; delta_qualifier ["inline_for_extraction"]];
  // Tac.dump "tac_extract";
  Tac.trefl ()

inline_for_extraction
let mk_reset (#input #result: Type) (#state: Type) (t: EE.esystem input state result) (stref: B.pointer state): ST unit
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  stref *= t.init

inline_for_extraction
let mk_step (#input #result: Type) (#state: Type) (t: EE.esystem input state result) (inp: input) (stref: B.pointer state) : ST result
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  let st  = !*stref in
  let (st', res): (state & result) = t.step inp st in
  stref *= st';
  res

