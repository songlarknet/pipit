(* Under-specified uint64 primitives for use in Pipit;
  Pipit doesn't support preconditions on primitives yet.
  TODO: This should be renamed to something like UInt64Underspec
  *)
module Network.TTCan.Prim.U64

module PSSB      = Pipit.Prim.HasStream

module REPR    = FStar.UInt64
module UInt    = FStar.UInt

let t = REPR.t

instance has_stream_U64: PSSB.has_stream t = {
  ty_id = [`%REPR.t];
  val_default = 0uL;
}

let valid (i: t): bool = UInt.fits (REPR.v i) REPR.n

let div_underspec (a b: t): r: t { REPR.v b <> 0 ==> r = REPR.div a b } =
  if b = 0uL then 0uL else REPR.div a b

let rem_underspec (a b: t): r: t { REPR.v b <> 0 ==> r = REPR.rem a b }  =
  if b = 0uL then 0uL else REPR.rem a b

(*** Infix notations *)
unfold let op_Plus           (a b: t): t = REPR.add_underspec a b
unfold let op_Subtraction    (a b: t): t = REPR.sub_underspec a b
unfold let op_Star           (a b: t): t = REPR.mul_underspec a b
unfold let op_Slash          (a b: t): t = div_underspec a b
unfold let op_Percent        (a b: t): t = rem_underspec a b
unfold let op_Hat            (a b: t): t = REPR.logxor a b
unfold let op_Amp            (a b: t): t = REPR.logand a b
unfold let op_Bar            (a b: t): t = REPR.logor a b
// unfold let op_Less_Less = REPR.shift_left
// unfold let op_Greater_Greater = shift_right
unfold let op_Greater        (a b: t): bool = REPR.gt a b
unfold let op_Greater_Equals (a b: t): bool = REPR.gte a b
unfold let op_Less           (a b: t): bool = REPR.lt a b
unfold let op_Less_Equals    (a b: t): bool = REPR.lte a b
