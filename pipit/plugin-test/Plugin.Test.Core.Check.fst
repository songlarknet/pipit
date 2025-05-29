module Plugin.Test.Core.Check

open Plugin.Test.Core.Basic

open Pipit.Source

module PPL = Pipit.Plugin.Lift
// module PPC = Pipit.Plugin.Check
module PSSB = Pipit.Sugar.Shallow.Base

module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table
module PXB  = Pipit.Exp.Base
module SI  = Pipit.System.Ind
module SX  = Pipit.System.Exp
module PT = Pipit.Tactics
module PXCB = Pipit.Exp.Checked.Base

// Useful for testing:
// #set-options "--ext pipit:lift:debug"
#set-options "--print_implicits --print_bound_var_types --print_full_names"

[@@source_mode (ModeFun Stream true Stream)]
let eg_check_trivial (x: int) =
  let prop = x < 0 || x >= 0 in
  check prop;
  x
%splice[eg_check_trivial_core] (PPL.lift_tac1 "eg_check_trivial")

[@@core_of_source (`%eg_check_trivial) (ModeFun Stream true Stream)]
let eg_check_trivial_check: PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int) =
  let e = eg_check_trivial_core in
  let sys = SX.system_of_exp e in
  assert (SI.induct1 sys) by (PT.norm_full []);
  PXCB.bless e

// %splice[eg_check_trivial_core_check] (PPC.check_tac1 "eg_check_trivial")

[@@source_mode (ModeFun Stream true Stream)]
let eg_check_false (x: int) =
  let prop = x > 0 in
  check prop;
  x
%splice[] (PPL.lift_tac1 "eg_check_false")

[@@core_of_source (`%eg_check_false) (ModeFun Stream true Stream); expect_failure]
let eg_check_false_check: PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int) =
  let e = eg_check_false_core in
  let sys = SX.system_of_exp e in
  assert (SI.induct1 sys) by (PT.norm_full []);
  PXCB.bless e

// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y


