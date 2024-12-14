module Plugin.Test.CoreLift

open Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
module PPI = Pipit.Plugin.Interface

// Useful for testing:
#push-options "--ext pipit:lift:debug"
#push-options "--print_implicits --print_bound_var_types --print_full_names"

instance has_stream_int: Pipit.Sugar.Shallow.Base.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

module PXB = Pipit.Exp.Base
module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table

[@@source_mode (ModeFun Stream true Stream)]
let eg_letincs_strm (x: int) =
  (x + x) + x

%splice[eg_letincs_strm_core] (PPL.lift_tac "eg_letincs_strm" "eg_letincs_strm_core" (ModeFun Stream true Stream))
