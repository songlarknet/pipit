(* TODO: let-binding shadowing where the RHS references the outer binding
   of the SAME NAME. The lifter resolves the inner reference against
   the new (not-yet-bound) `n`, producing
   `Error 230: Variable "n" not found`.

   Workaround in TTCan2 ports: rename the rebinding to a distinct
   name (e.g. `let m = ... in let n = m `fby` s in n`).

   Note: `[@@expect_failure]` cannot be placed on a `#lang-pipit` let
   because the auto-emitted splice is a separate sigelt. We use the
   manual `[@@source_mode ...]` + `%splice[] (PPL.lift_ast_tac1 ...)`
   pattern so the failure can be marked on the splice itself. *)
module Plugin.Test.Bug.LetShadow

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
open Pipit.Plugin.Interface
open Pipit.Source

(* Passing regression tests: shadow shapes that DO work today. *)

[@@source_mode (ModeFun Stream true Stream)]
let eg_shadow_let (s: int): int =
  let x = 0 `fby` s in
  let x = x + 1 in
  x
%splice[] (PPL.lift_ast_tac1 "eg_shadow_let")

[@@source_mode (ModeFun Stream true Stream)]
let eg_shadow_param (s: int): int =
  let s = s + 1 in
  s
%splice[] (PPL.lift_ast_tac1 "eg_shadow_param")

[@@source_mode (ModeFun Stream true Stream)]
let eg_shadow_double (s: int): int =
  let x = 0 `fby` s in
  let x = 0 `fby` x in
  let x = 0 `fby` x in
  x
%splice[] (PPL.lift_ast_tac1 "eg_shadow_double")

(* Known-failing shape: the RHS of the shadowing let references the
   outer binding of the SAME NAME. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_shadow_outer_in_rhs (s: int): int =
  let n = 1 in
  let n = n `fby` s in
  n
[@@expect_failure]
%splice[] (PPL.lift_ast_tac1 "eg_shadow_outer_in_rhs")
