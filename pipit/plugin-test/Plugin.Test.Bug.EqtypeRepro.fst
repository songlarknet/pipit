module Plugin.Test.Bug.EqtypeRepro

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
open Pipit.Plugin.Interface
open Pipit.Source

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
