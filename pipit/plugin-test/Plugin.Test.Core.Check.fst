module Plugin.Test.Core.Check

open Plugin.Test.Core.Basic

open Pipit.Source

module PPL = Pipit.Plugin.Lift
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

let eg_check_trivial_check_proof: PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int) =
  // let open Pipit.Sugar.Check in
  let e = eg_check_trivial_core [PSSB.shallow int] (PXB.XBase (PXB.XBVar 0)) in
  // let e: Pipit.Exp.Checked.Compound.cexp PPS.table [PSSB.shallow int] (PSSB.shallow int) = unsafe_coerce e in
  let sys = SX.system_of_exp e in
  assert (SI.induct1 sys) by (PT.norm_full []);
  // assert (system_induct_k1 e) by (PT.norm_full []);
  // assert (SI.system_holds_all sys);
  // assert (PXCB.check_all Pipit.Prop.Metadata.check_mode_unknown e);
  PXCB.bless e

let eg_check_trivial_check_weaken (ctx: PPT.context PPS.table) (xs: PXB.exp PPS.table ctx (PSSB.shallow int)): PXB.exp PPS.table ctx (PSSB.shallow int) =
    (PXB.XLet (PSSB.shallow int)
      xs
      (PXB.weaken ctx eg_check_trivial_check_proof))

[@@source_mode (ModeFun Stream true Stream)]
let eg_check_false (x: int) =
  let prop = x > 0 in
  check prop;
  x
%splice[] (PPL.lift_tac1 "eg_check_false")

// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y


