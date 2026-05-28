module Plugin.Test.Source.Record
#lang-pipit

(* Exercise record types in #lang-pipit source: construction, field
  projection, record update, nesting, recursion across record fields,
  records as input streams, and records as output streams. *)

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

#set-options "--warn_error -242"

[@@derive_has_stream]
type point = { px: int; py: int; }

[@@derive_has_stream]
type box = { tl: point; br: point; }


(*** 1. Record literal as output ***)

let mk_point (x: stream int) (y: stream int): stream point =
  { px = x; py = y }


(*** 2. Field projection from an input record stream ***)

let proj_x (p: stream point): stream int =
  p.px


(*** 3. Round-trip: project both fields then rebuild the record ***)

let rebuild (p: stream point): stream point =
  { px = p.px; py = p.py }


(*** 4. Arithmetic across projected fields ***)

let manhattan (p: stream point): stream int =
  let x = p.px in
  let y = p.py in
  (if x >= 0 then x else 0 - x) + (if y >= 0 then y else 0 - y)


(*** 5. Record update using [with] syntax ***)

let shift_x (p: stream point) (dx: stream int): stream point =
  { p with px = p.px + dx }


(*** 6. Nested records: project a field that is itself a record ***)

let top_left (b: stream box): stream point =
  b.tl

let nested_proj (b: stream box): stream int =
  b.tl.px


(*** 7. Build a nested record from two point streams ***)

let mk_box (a: stream point) (b: stream point): stream box =
  { tl = a; br = b }


(*** 8. [fby] on a whole record value ***)

let prev_point (p: stream point): stream point =
  { px = 0; py = 0 } `fby` p


(*** 9. Recursion across record fields ***)

let counter_xy (x: stream int) (y: stream int): stream point =
  let rec p =
    { px = 0 `fby` p.px + x
    ; py = 0 `fby` p.py + y
    }
  in p


(*** 10. Static (non-stream) record used inside a streaming function ***)

let with_offset (off: point) (p: stream point): stream point =
  { px = p.px + off.px; py = p.py + off.py }
