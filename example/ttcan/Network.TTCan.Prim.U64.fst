(* Under-specified uint64 primitives, embedded in Pipit.Shallow
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

let valid' (i: t): bool = UInt.fits (REPR.v i) REPR.n

let valid: Sugar.stream t -> Sugar.stream bool =
  SugarBase.liftP1 (Sugar.p'prim1 #t (Some [`%valid']) valid')

let add_underspec: Sugar.stream t -> Sugar.stream t -> Sugar.stream t =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.add_underspec]) REPR.add_underspec)

let sub_underspec: Sugar.stream t -> Sugar.stream t -> Sugar.stream t =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.sub_underspec]) REPR.sub_underspec)

let mul_underspec: Sugar.stream t -> Sugar.stream t -> Sugar.stream t =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.mul_underspec]) REPR.mul_underspec)

let div_underspec' (a b: t): r: t { REPR.v b <> 0 ==> r = REPR.div a b } =
  if b = 0uL then 0uL else REPR.div a b

let div_underspec: Sugar.stream t -> Sugar.stream t -> Sugar.stream t =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%div_underspec']) div_underspec')

let rem_underspec' (a b: t): r: t { REPR.v b <> 0 ==> r = REPR.rem a b }  =
  if b = 0uL then 0uL else REPR.rem a b

let rem_underspec: Sugar.stream t -> Sugar.stream t -> Sugar.stream t =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%rem_underspec']) rem_underspec')

let gt: Sugar.stream t -> Sugar.stream t -> Sugar.stream bool =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.gt]) REPR.gt)

let gte: Sugar.stream t -> Sugar.stream t -> Sugar.stream bool =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.gte]) REPR.gte)

let lt: Sugar.stream t -> Sugar.stream t -> Sugar.stream bool =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.lt]) REPR.lt)

let lte: Sugar.stream t -> Sugar.stream t -> Sugar.stream bool =
  SugarBase.liftP2 (Sugar.p'prim2 (Some [`%REPR.lt]) REPR.lte)

(*** Infix notations *)
unfold let op_Plus_Hat = add_underspec
unfold let op_Subtraction_Hat = sub_underspec
unfold let op_Subtraction_Question_Hat = sub_underspec
unfold let op_Star_Hat = mul_underspec
unfold let op_Slash_Hat = div_underspec
unfold let op_Percent_Hat = rem_underspec
// unfold let op_Hat_Hat = logxor
// unfold let op_Amp_Hat = logand
// unfold let op_Bar_Hat = logor
// unfold let op_Less_Less_Hat = shift_left
// unfold let op_Greater_Greater_Hat = shift_right
unfold let op_Greater_Hat = gt
unfold let op_Greater_Equals_Hat = gte
unfold let op_Less_Hat = lt
unfold let op_Less_Equals_Hat = lte
