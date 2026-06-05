module Plugin.Test.Bug.LocalUnfold2

(* Followup: the simple local-let test reduced unexpectedly. Now
   mimic the cexp situation more precisely: a CHAIN of local helpers
   (`__ctx_N = sty :: __ctx_(N-1)`) used inside a deeper term. *)

let rec get_index (#a: Type) (xs: list a) (i: nat { i < FStar.List.Tot.length xs }): a =
  match xs, i with
  | x :: _,  0 -> x
  | _ :: tl, _ -> get_index tl (i - 1)

(* === A. Chain via plain local lets, indexed at the END of the chain. === *)
let _A_chain_plain: unit =
  let c0 : list int = [99] in
  let c1 : list int = 10 :: c0 in
  let c2 : list int = 20 :: c1 in
  let c3 : list int = 30 :: c2 in
  // get_index c3 3 should reduce to 99 only if the WHOLE chain reduces.
  let _: (x: int { x == get_index c3 3 }) = 99 in
  ()

(* === B. Same chain but with `let unfold` at every level. === *)
let _B_chain_unfold: unit =
  let unfold c0 : list int = [99] in
  let unfold c1 : list int = 10 :: c0 in
  let unfold c2 : list int = 20 :: c1 in
  let unfold c3 : list int = 30 :: c2 in
  let _: (x: int { x == get_index c3 3 }) = 99 in
  ()

(* === C. Mimic the actual cexp situation more closely: index appears
   in a TYPE position (a refinement) that's INSIDE the type of a let
   binding whose body uses the chained ctx. === *)

let bound_at (xs: list int) (i: nat { i < FStar.List.Tot.length xs }) (v: int { v == get_index xs i }): int = v

let _C_chain_type_position: unit =
  let c0 : list int = [99] in
  let c1 : list int = 10 :: c0 in
  let c2 : list int = 20 :: c1 in
  let c3 : list int = 30 :: c2 in
  // Calling bound_at forces F* to unify v's refinement type, which
  // requires reducing get_index c3 3.
  let _ = bound_at c3 3 99 in
  ()
