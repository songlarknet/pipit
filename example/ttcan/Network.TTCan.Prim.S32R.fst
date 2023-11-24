(* Signed 32-bit integers with a statically-known range.
  The range is inclusive.
  Operations are generally saturating.
*)
module Network.TTCan.Prim.S32R

module Sugar     = Pipit.Sugar.Shallow
module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics
module U64X      = Network.TTCan.Prim.U64

module REPR    = FStar.Int32
module Int     = FStar.Int
module Cast    = FStar.Int.Cast
module U64     = FStar.UInt64

type bound = i: int { Int.fits i REPR.n }
type bounds = { min: bound; max: max: bound { min <= max }}

type t (b: bounds) = { repr: s32: REPR.t { b.min <= REPR.v s32 /\ REPR.v s32 <= b.max } }

let s32r' (#b: bounds) (x: int { b.min <= x /\ x <= b.max }): t b =
  { repr = REPR.int_to_t x }

instance has_stream_S32R (b: bounds): Sugar.has_stream (t b) = {
  ty_id = [`%t; string_of_int b.min; string_of_int b.max];
  val_default = s32r' b.min;
}


let inc_sat' (#b: bounds) (x: t b): t b =
  if REPR.v x.repr < b.max
  then { repr = REPR.add x.repr 1l }
  else x

let dec_sat' (#b: bounds) (x: t b): t b =
  if REPR.v x.repr > b.min
  then { repr = REPR.sub x.repr 1l }
  else x

let extend' (#b: bounds) (#b': bounds { b'.min <= b.min /\ b.max <= b'.max }) (x: t b): t b' =
  { repr = x.repr }

let s32r_to_u64' (#b: bounds { 0 <= b.min }) (x: t b): U64.t =
  let r = Cast.int32_to_uint64 x.repr in
  assert (U64.v r == REPR.v x.repr);
  r

// TODO add saturated operations...
// let add_sat': t min max -> t min max -> t min max =
// let div_underspec' (a b: t min max): r: t { REPR.v b <> 0 ==> r = REPR.div a b } =
//   if b = 0uL then 0uL else REPR.div a b

// very under-specified rem: requires minimum bound to be 0 to avoid overflows like -32768/-1
let rem_underspec' (#b: bounds { b.min == 0 }) (x y: t b): t b  =
  // refinement? { REPR.v y.repr <> 0 ==> REPR.v r.repr == REPR.v x.repr % REPR.v y.repr }
  if REPR.v y.repr <> 0 then begin
    let r = REPR.rem x.repr y.repr in
    { repr = r }
  end else
    { repr = 0l }



let gt'  (#b: bounds) (x y: t b): bool = REPR.gt  x.repr y.repr
let gte' (#b: bounds) (x y: t b): bool = REPR.gte x.repr y.repr
let lt'  (#b: bounds) (x y: t b): bool = REPR.lt  x.repr y.repr
let lte' (#b: bounds) (x y: t b): bool = REPR.lte x.repr y.repr


let s32r (#b: bounds) (x: int { b.min <= x /\ x <= b.max }): Sugar.stream (t b) =
  Sugar.const (s32r' #b x)

%splice[inc_sat] (SugarTac.lift_prim "inc_sat" (`inc_sat'))
%splice[dec_sat] (SugarTac.lift_prim "dec_sat" (`dec_sat'))
%splice[extend] (SugarTac.lift_prim "extend" (`extend'))
%splice[s32r_to_u64] (SugarTac.lift_prim "s32r_to_u64" (`s32r_to_u64'))

%splice[rem_underspec] (SugarTac.lift_prim "rem_underspec" (`rem_underspec'))
%splice[gt]  (SugarTac.lift_prim "gt"  (`gt'))
%splice[gte] (SugarTac.lift_prim "gte" (`gte'))
%splice[lt]  (SugarTac.lift_prim "lt"  (`lt'))
%splice[lte] (SugarTac.lift_prim "lte" (`lte'))

(*** Infix notations *)
// unfold let op_Plus = add_underspec
// unfold let op_Subtraction = sub_underspec
// unfold let op_Star = mul_underspec
// unfold let op_Slash = div_underspec
unfold let op_Percent (#b: bounds { b.min == 0 }) = rem_underspec #b
// unfold let op_Hat = logxor
// unfold let op_Amp = logand
// unfold let op_Bar = logor
// unfold let op_Less_Less = shift_left
// unfold let op_Greater_Greater = shift_right
unfold let op_Greater (#b: bounds) = gt #b
unfold let op_Greater_Equals (#b: bounds) = gte #b
unfold let op_Less (#b: bounds) = lt #b
unfold let op_Less_Equals (#b: bounds) = lte #b
