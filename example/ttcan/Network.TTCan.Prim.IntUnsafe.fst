(* Unsafe (overflow unchecked) integers *)
module Network.TTCan.Prim.IntUnsafe

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

instance has_stream_int: Sugar.has_stream int = {
  ty_id = [`%int];
  val_default = 0;
  val_eq      = (fun a b -> a = b);
}

%splice[] (SugarTac.lift_prim "op_Plus" (`op_Addition))
%splice[] (SugarTac.lift_prim "op_Subtraction" (`op_Subtraction))
%splice[] (SugarTac.lift_prim "op_Star" (`op_Multiply))
// %splice[] (SugarTac.lift_prim "op_Slash" (`op_Division))
// %splice[] (SugarTac.lift_prim "op_Percent" (`op_Modulus))
%splice[] (SugarTac.lift_prim "op_Greater" (`op_GreaterThan))
%splice[] (SugarTac.lift_prim "op_Greater_Equals" (`op_GreaterThanOrEqual))
%splice[] (SugarTac.lift_prim "op_Less" (`op_LessThan))
%splice[] (SugarTac.lift_prim "op_Less_Equals" (`op_LessThanOrEqual))
