module Plugin.Test.Bug.LocalUnfold

(* Empirical test: does local `let unfold x = e` affect F*'s
   type-level unifier/normalizer the way top-level `unfold let` does?

   Setup mirrors the cexp case: a recursive function `get_index` that
   only reduces if its list argument exposes a `Cons` head; bind the
   list as a local helper; ask F* to typecheck a term whose type
   depends on `get_index helper i` reducing. *)

let rec get_index (#a: Type) (xs: list a) (i: nat { i < FStar.List.Tot.length xs }): a =
  match xs, i with
  | x :: _,  0 -> x
  | _ :: tl, _ -> get_index tl (i - 1)

(* Baseline: top-level `unfold let` (what `flush_ctx_acc` emits). *)
unfold
let ctx_top : list int = [10; 20; 30]

let _check_top: (x: int { x == get_index ctx_top 1 }) = 20

(* Experiment 1: local `let unfold`. *)
let _check_local_unfold: unit =
  let unfold ctx_local : list int = [10; 20; 30] in
  let _: (x: int { x == get_index ctx_local 1 }) = 20 in
  ()

(* Experiment 2: plain local `let` (control — expected to leave
   `get_index ctx_local 1` stuck). *)
[@@expect_failure]
let _check_local_plain: unit =
  let ctx_local : list int = [10; 20; 30] in
  let _: (x: int { x == get_index ctx_local 1 }) = 20 in
  ()
