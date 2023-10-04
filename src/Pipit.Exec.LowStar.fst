(* Simple, inefficient integration with C. *)
module Pipit.Exec.LowStar

module EE = Pipit.Exec.Exp

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
let mk_reset (#input #result: Type) (#state: Type) (t: EE.esystem input state result) (stref: B.pointer state): ST unit
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  stref *= t.init

[@@strict_on_arguments [4]]
inline_for_extraction
let mk_step (#input #result: Type) (#state: Type) (t: EE.esystem input state result) (inp: input) (stref: B.pointer state) : ST result
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  let st  = !*stref in
  let (st', res): (state & result) = t.step inp st in
  stref *= st';
  res

