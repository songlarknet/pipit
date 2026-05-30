module Plugin.Test
#lang-pipit

#set-options "--ext pipit:lift:debug"

open Pipit.Source

let eg_letrec_mut (x: stream int) =
  let rec a = x + b
      and b = x - a
  in a


let eg_inc_left_strm (x: stream int) =
  x + 1

let eg_inc_right_strm (x: stream int) =
  1 + x

let eg_additions_strm (x: stream int) =
  (x + x) + x

let eg_additions_strm_ret_ann (x: stream int): stream int =
  (x + x) + x

let eg_fby (x: stream int) =
  0 `fby` x

let eg_fby_inc (x: stream int) =
  0 `fby` x + 1

(* TEMPORARILY DISABLED: `let rec count x = ...` is a recursive *function*,
   not a non-function recursive stream definition; the new pipeline only
   supports the latter (via the `rec'` rewrite). *)
(*
let eg_letrecfun (x: stream int): stream int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0
*)

let eg_let_strm (x: stream int) =
  let strm = x + 1 in
  strm + x

let eg_let_strm_ann (x: stream int): stream int =
  let strm: stream int = 1 in
  strm + x

let eg_let_stat (x: stream int): stream int =
  let stat = 1 in
  x + stat

let eg_rec_strm (x: stream int) =
  let rec count = 0 `fby` count + 1 in
  count

let eg_rec_strm_let_stat (x: stream int) =
  let rec count1 = 0 `fby` count1 + 1 in
  let static1: int = 0 in
  count1 + static1

let eg_mixed_ann (x: stream int) =
  let rec count1 = 0 `fby` count1 + 1 in
  let rec count2: stream int = 0 `fby` count2 + 1 in
  let strm1: stream int = 0 in
  let strm2: stream int = 0 in
  let strm3 = count1 + strm1 in
  let static1: int = 0 in
  let static2 = 0 in
  count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

let eg_pairs (x: stream int) (y: stream bool): stream int =
  0 `fby` fst (x, y)

[@@derive_has_stream]
type ctor = | Ctor: x: int -> y: int -> ctor

let eg_ctor (add: stream int) =
  let rec rcd =
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

let eg_pairsrec (add: stream int) =
  let rec xy =
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y)
  in
  xy

[@@derive_has_stream]
type record = { x: int; y: int; }

let eg_record (add: stream int) =
  let x = 0 `fby` add in
  let y = 1 `fby` add in
  let xy = { x; y } in
  xy.x


// TODO match
let eg_streaming_if (x: stream int) =
  if x >= 0 then x else -x

// %splice[] (PPL.lift_tac1 "eg_streaming_if")

let eg_streaming_match_lets (x: stream int): stream int =
  let cond = x >= 0 in
  let abs =
    match cond with
      | true -> x
      | false -> -x
  in abs

// %splice[] (autolift_binds [`%eg_streaming_match_lets])

(* Static multi-arm match: `consts` is a static `list int`, the arm
   bodies are streams. Lifted via `AMatch AppPureConst`; the match is
   re-emitted as a plain F* `Tv_Match` in Lower and resolves at each
   call site. *)
let eg_static_match (consts: list int) (x: stream int) =
  match consts with
  | [] -> 0
  | (c: int) :: _ -> c + x

(* Refinement on `silly_id`'s return type is stripped by `strip_refinements`
   in `Pipit.Source.Ast.OfFStar`, so `lb_typ` ends up with a plain `int`. *)
let silly_id (x: int): y: int { x == y } = x

let eg_refinement0 (x: stream int) =
  silly_id x

let eg_streaming_letmatch (xy: stream (int & int)): stream int =
  let (x, y) = xy in
  x + y

(*** Not supported examples ***)


// streaming matches cannot bind variables:

// maybe clocked streaming matches should use match^ syntax
// eg unclocked:
// u = if a then (0 `fby` x) else (0 `fby` y)
// u(t) = if a(t) then x(t - 1) else y(t - 1)
// vs clocked:
// c = if^ a then (0 `fby` x) else (0 `fby` y)
// c(t) = if a(t) then x(max { t' | a(t'), t' < t }) else y(max { t' | !a(t') /\ t' < t })

// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match^ x with
//   | Some e -> e
//   | None -> 0

// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y
