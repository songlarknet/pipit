(* Simple, inefficient integration with C. *)
module Pipit.Exec.LowStar

module X = Pipit.Exec.Base

module B = LowStar.Buffer
module Tac = FStar.Tactics

open LowStar.BufferOps
open FStar.HyperStack.ST

(* Tactic for normalizing *)
let tac_extract () =
  Tac.norm [nbe; delta; primops; iota; zeta];
  Tac.trefl ()

inline_for_extraction
let mk_reset (#input #state #result: Type) (t: X.exec input state result) (stref: B.pointer state): ST unit
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  stref *= t.init

inline_for_extraction
let mk_step (#input #state #result: Type) (t: X.exec input state result) (inp: input) (stref: B.pointer state) : ST result
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  let st  = !*stref in
  let res = t.eval inp st in
  let st' = t.update inp st in
  stref *= st';
  res

