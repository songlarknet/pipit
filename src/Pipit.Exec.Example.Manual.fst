(* Manual translation example *)
module Pipit.Exec.Example.Manual

open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module MO = LowStar.Modifies

open FStar.HyperStack.ST

let init (state: B.pointer int): ST unit
    (requires (fun h -> B.live h state))
    (ensures (fun h _ h' -> B.live h' state)) =
  state *= 0

let eval (state: B.pointer int) (input: bool): ST int
    (requires (fun h -> B.live h state))
    (ensures (fun h _ h' -> B.live h' state)) =
  let c = !* state in
  c + (if input then 1 else 0)

let update (state: B.pointer int) (input: bool): ST unit
    (requires (fun h -> B.live h state))
    (ensures (fun h _ h' -> B.live h' state)) =
  let count' = eval state input in
  state *= count'
