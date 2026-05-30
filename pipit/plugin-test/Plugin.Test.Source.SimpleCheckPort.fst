(* Experimental port of `Example.Simple.Check` to the new AST pipeline
   (`lift_ast_tac1`), without `#lang-pipit`. Used to confirm what works
   and to flush out any remaining gaps. As of 2026-05-28, all 8
   originally-tested bindings lift cleanly here, including
   `times_guarantee` (after fixing implicit-polymorphic primitive
   handling in `of_prim_fv`, see `Plugin.Test.Bug.EqtypeRepro`). *)
module Plugin.Test.Source.SimpleCheckPort

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
open Pipit.Plugin.Interface
open Pipit.Source

(* ----- 1. count_when: rec' + fby + if + arg-as-stream ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let count_when (p: bool): int =
  rec' (fun count -> (0 `fby` count) + (if p then 1 else 0))
%splice[] (PPL.lift_ast_tac1 "count_when")

(* ----- 2. sum_impl: rec' + fby + cross-binder var ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let sum_impl (i: int): int =
  rec' (fun sum -> (0 `fby` sum) + i)
%splice[] (PPL.lift_ast_tac1 "sum_impl")

(* ----- 3. test_sum_impl: ACallStream into sum_impl ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let test_sum_impl (i: int): int =
  let arg = if i > 0 then i else 1 in
  sum_impl arg
%splice[] (PPL.lift_ast_tac1 "test_sum_impl")

(* ----- 4. count_when_prop_body: 3 ACallStreams + 3 sequenced checks ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let count_when_prop_body (e: bool): unit =
  let count_when_false = count_when false in
  let count_when_e = count_when e in
  let count_when_true = count_when true in
  check (0 <= count_when_false);
  check (count_when_false <= count_when_e);
  check (count_when_e <= count_when_true)
%splice[] (PPL.lift_ast_tac1 "count_when_prop_body")

(* ----- 5. count_when_prop_body2: 2-arg variant ----- *)

[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let count_when_prop_body2 (e: bool) (f: bool): unit =
  let count_when_e = count_when e in
  let count_when_f = count_when f in
  let count_when_true = count_when true in
  check (count_when_e <= count_when_true);
  check (count_when_f <= count_when_true)
%splice[] (PPL.lift_ast_tac1 "count_when_prop_body2")

(* ----- 6. sum_rely / sum_guarantee: plain bool predicates ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let sum_rely (i: int): bool = i > 0
%splice[] (PPL.lift_ast_tac1 "sum_rely")

[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let sum_guarantee (sum i: int): bool = sum > (0 `fby` sum)
%splice[] (PPL.lift_ast_tac1 "sum_guarantee")

(* ----- 7. test_sum_checked_impl: let + ACallStream + check + return ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let test_sum_checked_impl (i: int): int =
  let arg = if i > 0 then i else 1 in
  let sarg = sum_impl arg in
  check (sarg > (0 `fby` sarg));
  sarg
%splice[] (PPL.lift_ast_tac1 "test_sum_checked_impl")

(* ----- 8. times_guarantee: heavy boolean / int primitive load + abs ----- *)

[@@source_mode (ModeFun Stream true (ModeFun Stream true (ModeFun Stream true Stream)))]
let times_guarantee (x y z: int): bool =
  let abs_x = abs x in
  let abs_y = abs y in
  let abs_z = abs z in
  ((z = y) = ((x = 1) || (y = 0))) &&
  ((z = x) = ((y = 1) || (x = 0))) &&
  ((z = 0) = ((x = 0) || (y = 0))) &&
  ((z > 0) = (((x > 0) && (y > 0)) || ((x < 0) && (y < 0)))) &&
  ((z < 0) = (((x > 0) && (y < 0)) || ((x < 0) && (y > 0)))) &&
  ((abs_z >= abs_y) = ((abs_x >= 1) || (y = 0))) &&
  ((abs_z >= abs_x) = ((abs_y >= 1) || (x = 0))) &&
  ((abs_z <= abs_y) = ((abs_x <= 1) || (y = 0))) &&
  ((abs_z <= abs_x) = ((abs_y <= 1) || (x = 0)))
%splice[] (PPL.lift_ast_tac1 "times_guarantee")
