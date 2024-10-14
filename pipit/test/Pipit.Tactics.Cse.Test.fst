module Pipit.Tactics.Cse.Test

open Pipit.Tactics.Cse

module List = FStar.List.Tot

module Tac = FStar.Tactics

#push-options "--ext pipit:cse:debug"
#push-options "--print_implicits --print_bound_var_types"
// #push-options "--print_full_names"
// #push-options "--print_implicits --print_full_names --ugly --print_bound_var_types"

(*** Examples / test cases ***)
// [@@Tac.preprocess_with cse]
// let eg_addns (x: int) =
//   (x + x) + x

[@@Tac.preprocess_with cse]
let eg_letrecfun (y: int): int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0
