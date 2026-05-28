module Plugin.Test.Polymorphic
#lang-pipit

(* Can we use base `FStar.Pervasives.Native.fst`/`snd` directly (as
   primitive projector lifts) without the local typeclass-wrapped
   shims defined in `Plugin.Test`? *)

#set-options "--ext pipit:lift:debug"

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

let eg_pairs_base (x: stream int) (y: stream bool): stream int =
  0 `fby` fst (x, y)

let eg_pairsrec_base (add: stream int) =
  let rec xy =
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y)
  in
  xy


(*** User-defined polymorphic stream combinators over `has_stream`.

  Each combinator is parameterised over one or more `#a:eqtype` with a
  `{| has_stream a |}` constraint and is invoked from a monomorphic
  consumer below so the splice has concrete types to lift. *)

(* 1. Polymorphic identity on streams. *)
let poly_id (#a: eqtype) {| PSSB.has_stream a |} (x: stream a): stream a =
  x

let use_poly_id_int (x: stream int): stream int =
  poly_id x

let use_poly_id_bool (b: stream bool): stream bool =
  poly_id b

(* 2. Polymorphic duplication into a pair. *)
let poly_dup (#a: eqtype) {| PSSB.has_stream a |} (x: stream a): stream (a & a) =
  (x, x)

let use_poly_dup_int (x: stream int): stream int =
  let xx = poly_dup x in
  fst xx + snd xx

(* 3. Polymorphic pair swap (consumes and produces tuple streams). *)
let poly_swap (#a #b: eqtype) {| PSSB.has_stream a |} {| PSSB.has_stream b |}
  (xy: stream (a & b)): stream (b & a) =
  (snd xy, fst xy)

let use_poly_swap_intbool (x: stream int) (y: stream bool): stream bool =
  let yx = poly_swap (x, y) in
  fst yx

(* 4. Polymorphic projection composition: `fst` after `swap` = `snd`. *)
let poly_first_after_swap
  (#a #b: eqtype) {| PSSB.has_stream a |} {| PSSB.has_stream b |}
  (xy: stream (a & b)): stream b =
  fst (poly_swap xy)

let use_first_after_swap (x: stream int) (y: stream bool): stream bool =
  poly_first_after_swap (x, y)

(* 5. Polymorphic combinator used inside a `rec'` over a pair stream. *)
let poly_swap_rec (add: stream int) =
  let rec xy =
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    poly_swap (x, y)
  in
  xy

