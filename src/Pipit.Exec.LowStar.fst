(* Shitty C translation *)
module Pipit.Exec.LowStar

// open Pipit.Exp.Base

module X = Pipit.Exec.Base

open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module MO = LowStar.Modifies

open FStar.HyperStack.ST

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

module Tac = FStar.Tactics

let tac_post () =
  Tac.norm [nbe; delta; primops; iota; zeta; delta_fully ["Pipit.System.ExpX.values_index"]];
  Tac.trefl ()
