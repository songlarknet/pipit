(* Under-specified uint64 primitives for use in Pipit;
  Pipit doesn't support preconditions on primitives yet.
  TODO: This should be renamed to something like UInt64Underspec
  *)
module Network.TTCan.Prim.U64

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base

module REPR    = FStar.UInt64
module UInt    = FStar.UInt

let t = REPR.t

instance has_stream_U64: Sugar.has_stream t = {
  ty_id = [`%REPR.t];
  val_default = 0uL;
}

let valid (i: t): bool = UInt.fits (REPR.v i) REPR.n

let div_underspec (a b: t): r: t { REPR.v b <> 0 ==> r = REPR.div a b } =
  if b = 0uL then 0uL else REPR.div a b

let rem_underspec (a b: t): r: t { REPR.v b <> 0 ==> r = REPR.rem a b }  =
  if b = 0uL then 0uL else REPR.rem a b

(*** Infix notations *)
unfold let op_Plus = REPR.add_underspec
unfold let op_Subtraction = REPR.sub_underspec
unfold let op_Star = REPR.mul_underspec
unfold let op_Slash = div_underspec
unfold let op_Percent = rem_underspec
unfold let op_Hat = REPR.logxor
unfold let op_Amp = REPR.logand
unfold let op_Bar = REPR.logor
// unfold let op_Less_Less = REPR.shift_left
// unfold let op_Greater_Greater = shift_right
unfold let op_Greater = REPR.gt
unfold let op_Greater_Equals = REPR.gte
unfold let op_Less = REPR.lt
unfold let op_Less_Equals = REPR.lte
