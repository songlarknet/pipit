module Plugin.Test.Bug.LocalUnfold4

(* The cexp pattern: many subterms share the SAME ctx in their TYPES,
   so each subterm gets independently typed and the resulting types
   must unify pairwise. With top-level `unfold let`, the unifier can
   delta+zeta both sides cheaply. With raw `Tv_Let` shared in the
   surrounding context, does the unifier still unify two
   `get_index ctx 1` occurrences in different subterms? *)

let rec get_index (#a: Type) (xs: list a) (i: nat { i < FStar.List.Tot.length xs }): a =
  match xs, i with
  | x :: _,  0 -> x
  | _ :: tl, _ -> get_index tl (i - 1)

(* `at` produces a value with a SHARP type mentioning get_index xs i.
   Two `at xs i` calls have types that must unify by reducing
   get_index xs i. *)
let at (xs: list int) (i: nat { i < FStar.List.Tot.length xs }): (x: int { x == get_index xs i }) =
  get_index xs i

(* `pair_eq` requires the two arguments' refinement types to AGREE
   (so the two get_index calls must reduce to the same int). *)
let pair_eq (#v: int) (a: (x: int { x == v })) (b: (x: int { x == v })): bool = a = b

(* === A. Plain local let, large chain, many uses requiring pairwise unification. === *)
let _A_many_uses_plain: bool =
  let c0 : list int = [9] in
  let c1 = 1 :: c0 in
  let c2 = 2 :: c1 in
  let c3 = 3 :: c2 in
  let c4 = 4 :: c3 in
  let c5 = 5 :: c4 in
  // Each `at c5 i` returns a value whose type is `x == get_index c5 i`.
  // pair_eq forces unification of the two types.
  let _ = pair_eq #(get_index c5 0) (at c5 0) (at c5 0) in
  let _ = pair_eq #(get_index c5 1) (at c5 1) (at c5 1) in
  let _ = pair_eq #(get_index c5 2) (at c5 2) (at c5 2) in
  let _ = pair_eq #(get_index c5 3) (at c5 3) (at c5 3) in
  let _ = pair_eq #(get_index c5 4) (at c5 4) (at c5 4) in
  let _ = pair_eq #(get_index c5 5) (at c5 5) (at c5 5) in
  true

(* === B. Same with `let unfold`. === *)
let _B_many_uses_unfold: bool =
  let unfold c0 : list int = [9] in
  let unfold c1 = 1 :: c0 in
  let unfold c2 = 2 :: c1 in
  let unfold c3 = 3 :: c2 in
  let unfold c4 = 4 :: c3 in
  let unfold c5 = 5 :: c4 in
  let _ = pair_eq #(get_index c5 0) (at c5 0) (at c5 0) in
  let _ = pair_eq #(get_index c5 1) (at c5 1) (at c5 1) in
  let _ = pair_eq #(get_index c5 2) (at c5 2) (at c5 2) in
  let _ = pair_eq #(get_index c5 3) (at c5 3) (at c5 3) in
  let _ = pair_eq #(get_index c5 4) (at c5 4) (at c5 4) in
  let _ = pair_eq #(get_index c5 5) (at c5 5) (at c5 5) in
  true
