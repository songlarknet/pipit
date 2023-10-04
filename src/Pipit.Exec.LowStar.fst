(* Simple, inefficient integration with C. *)
module Pipit.Exec.LowStar

module SB = Pipit.System.Base
module SX = Pipit.System.Exec

module B = LowStar.Buffer
module Tac = FStar.Tactics

open LowStar.BufferOps
open FStar.HyperStack.ST

(* Tactic for normalizing *)
let tac_extract () =
  Tac.norm [nbe; delta; primops; iota; zeta];
  Tac.trefl ()

(* This `strict_on_arguments` annotation is mentioned in the Noise* paper [1],
   but I'm not sure if it's strictly necessary here. We still need to apply NBE
   with the above tactic even after specifying this, but maybe that just means
   I'm missing some other applications.

   [1] https://eprint.iacr.org/2022/607.  *)
[@@strict_on_arguments [4]]
inline_for_extraction
let mk_reset (#input #result: Type) (#state: option Type) (t: SX.esystem input state result) (stref: B.pointer (SB.option_type_sem state)): ST unit
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  stref *= t.init

[@@strict_on_arguments [4]]
inline_for_extraction
let mk_step (#input #result: Type) (#state: option Type) (t: SX.esystem input state result) (inp: input) (stref: B.pointer (SB.option_type_sem state)) : ST result
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  let st  = !*stref in
  let (st', res): (SB.option_type_sem state & result) = t.step inp st in
  stref *= st';
  res

