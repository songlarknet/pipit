module Pipit.Sugar.Shallow.Tactics.Lift.Test

open Pipit.Sugar.Shallow.Tactics.Lift

module Shallow = Pipit.Sugar.Shallow.Base

module List = FStar.List.Tot

module Tac = FStar.Tactics

// Don't warn on local let-recs; they're only for testing
#push-options "--warn_error -242"

// Useful for testing:
#push-options "--ext pipit:lift:debug"
#push-options "--print_implicits --print_bound_var_types --print_full_names"

instance has_stream_int: Shallow.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

(*** Examples / test cases ***)
[@@source]
let eg_letincs (x: stream int) =
  (x + x) + x

%splice[] (autolift_binds [`%eg_letincs])

[@@source]
let eg_letincs_ann (x: stream int): stream int =
  (x + x) + x

%splice[] (autolift_binds [`%eg_letincs_ann])

[@@source]
let eg_fby (x: stream int): stream int =
  0 `fby` x

%splice[] (autolift_binds [`%eg_fby])

[@@source]
let eg_fby_inc (x: stream int): stream int =
  0 `fby` x + 1

%splice[] (autolift_binds [`%eg_fby_inc])

[@@Tac.preprocess_with preprocess; source]
let eg_letrecfun (x: int): int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0

%splice[] (autolift_binds [`%eg_letrecfun])

[@@source]
let eg_letrecfun_ann (x: int): int =
  let rec count (x: int): int = if x > 0 then count (x - 1) else 0 in
  count 0

%splice[] (autolift_binds [`%eg_letrecfun_ann])

[@@Tac.preprocess_with preprocess; source]
let eg_let (x: stream int): stream int =
  let strm = x + 1 in
  strm

%splice[] (autolift_binds [`%eg_let])

[@@Tac.preprocess_with preprocess; source]
let eg_let_ann (x: stream int): stream int =
  let strm: stream int = x + 1 in
  strm

%splice[] (autolift_binds [`%eg_let_ann])

[@@Tac.preprocess_with preprocess; source]
let eg_letrec (x: stream int): stream int =
  let rec count = 0 `fby` count + 1 in
  count

%splice[] (autolift_binds [`%eg_letrec])

[@@Tac.preprocess_with preprocess; source]
let eg_mixed_ann (x: stream int): stream int =
  let rec count1 = 0 `fby` count1 + 1 in
  let rec count2: stream int = 0 `fby` count2 + 1 in
  let strm1: stream int = 0 in
  let strm2 = 0 <: stream int in
  let strm3 = count1 + strm1 in
  let static1: int = 0 in
  let static2 = 0 in
  count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

%splice[] (autolift_binds [`%eg_mixed_ann])

let eg_pairs (x: stream int) (y: stream bool): stream int =
  0 `fby` fst (Mktuple2 x y)

%splice[] (autolift_binds [`%eg_pairs])


type ctor = | Ctor: x: int -> y: int -> ctor
instance has_stream_ctor: Shallow.has_stream ctor = {
  ty_id       = [`%ctor];
  val_default = Ctor Shallow.val_default Shallow.val_default;
}

[@@Tac.preprocess_with preprocess]
let eg_ctor (add: stream int): stream ctor =
  let rec rcd =
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

%splice[] (autolift_binds [`%eg_ctor])

[@@Tac.preprocess_with preprocess]
let eg_pairsrec (add: stream int): stream (int & int) =
  // recursive streams sometimes need annotations
  let rec xy: stream (int & int) =
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y)
  in
  xy

%splice[] (autolift_binds [`%eg_pairsrec])

type record = { x: int; y: int; }

instance has_stream_record: Shallow.has_stream record = {
  ty_id       = [`%record];
  val_default = { x = 0; y = 0; };
}


// XXX:TODO: preprocess breaks on records?
[@@Tac.preprocess_with preprocess; source]
let eg_record (add: stream int): stream int =
  let x = 0 `fby` add in
  let y = 1 `fby` add in
  let xy = { x; y } in
  xy.x


%splice[] (autolift_binds [`%eg_record])

let eg_streaming_if (x: stream int): stream int =
  if x >= 0 then x else -x

%splice[] (autolift_binds [`%eg_streaming_if])

let eg_streaming_match_lets (x: stream int): stream int =
  let cond = x >= 0 in
  let abs =
    match cond with
      | true -> x
      | false -> -x
  in abs

%splice[] (autolift_binds [`%eg_streaming_match_lets])

let eg_static_match (consts: list int) (x: stream int): stream int =
  match consts with
  | [] -> 0
  | (c: int) :: _ -> c + x

%splice[] (autolift_binds [`%eg_static_match])

let silly_id (x: int): y: int { x == y } = x

(*** Examples / test cases ***)
[@@source]
let eg_refinement0 (x: stream int): stream int =
  silly_id x

%splice[] (autolift_binds [`%eg_refinement0])

(*** Not supported examples ***)


// mutual recursion not supported:

// [@@Tac.preprocess_with tac_lift]
// let eg_letrec_mut (x: int): int =
//   let rec a = x + b
//       and b = x - a
//   in a

// streaming matches cannot bind variables:

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match x with
//   | Some e -> e
//   | None -> 0

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_letmatch (xy: stream (int & int)): stream int =
//   let (x, y) = xy in
//   x + y

// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y

// %splice[] (autolift_binds [`%eg_instantiate_lemma])
