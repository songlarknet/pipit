(* Signed 32-bit integers with a statically-known range.
  The range is inclusive.
  Operations are generally saturating.
*)
module Network.TTCan.Prim.S32R

module Sugar     = Pipit.Sugar.Shallow

module REPR    = FStar.Int32
module Int     = FStar.Int
module Cast    = FStar.Int.Cast
module U8      = FStar.UInt8
module U64     = FStar.UInt64

module Math    = FStar.Math.Lemmas

type bound = i: int { Int.fits i REPR.n }
type bounds = { min: bound; max: max: bound { min <= max }}

type t (b: bounds) = { repr: s32: REPR.t { b.min <= REPR.v s32 /\ REPR.v s32 <= b.max } }

let v (#b: bounds) (r: t b): i: int { b.min <= i /\ i <= b.max } =
  REPR.v r.repr

let s32r (#b: bounds) (x: int { b.min <= x /\ x <= b.max })
  : s: t b { v s == x } =
  { repr = REPR.int_to_t x }

// disable instance: each instance should instantiate itself
let has_stream_S32R (b: bounds): Sugar.has_stream (t b) = {
  ty_id = [`%t; string_of_int b.min; string_of_int b.max];
  val_default = s32r b.min;
}



let inc_sat (#b: bounds) (x: t b)
  : s: t b { v s >= v x /\ v s <= v x + 1 /\ (v s < b.max ==> v s = v x + 1) } =
  if x.repr `REPR.lt` REPR.int_to_t b.max
  then { repr = REPR.add x.repr 1l }
  else x

let dec_sat (#b: bounds) (x: t b)
  : s: t b { v s <= v x /\ v s >= v x - 1 /\ (v s > b.min ==> v s = v x - 1)} =
  if x.repr `REPR.gt` REPR.int_to_t b.min
  then { repr = REPR.sub x.repr 1l }
  else x

let extend (#b: bounds) (#b': bounds { b'.min <= b.min /\ b.max <= b'.max }) (x: t b)
  : s: t b' { v s == v x } =
  { repr = x.repr }

let shrink (#b: bounds) (#b': bounds) (x: t b { b'.min <= v x /\ v x <= b'.max })
  : s: t b' { v s == v x } =
  { repr = x.repr }

let s32r_to_u64 (#b: bounds { 0 <= b.min }) (x: t b)
  : r: U64.t { U64.v r == v x } =
  let r = Cast.int32_to_uint64 x.repr in
  assert (U64.v r == v x);
  r

let s32r_to_u8 (#b: bounds { 0 <= b.min /\ b.max <= 255 }) (x: t b)
  : r: U8.t { U8.v r == v x } =
  let r = Cast.int32_to_uint8 x.repr in
  assert (U8.v r == v x);
  r

let u64_to_s32r (#b: bounds) (x: U64.t { b.min <= U64.v x /\ U64.v x <= b.max }): t b =
  // Deprecated, but this is a safe usage
  let r = { repr = Cast.uint64_to_int32 x } in
  assert (v r == U64.v x);
  r

let u8_to_s32r (#b: bounds) (x: U8.t { b.min <= U8.v x /\ U8.v x <= b.max }): t b =
  let r = { repr = Cast.uint8_to_int32 x } in
  assert (v r == U8.v x);
  r

// TODO implement remaining saturated operations...

let clamp (#b: bounds) (x: REPR.t): t b =
  let min = REPR.int_to_t b.min in
  let max = REPR.int_to_t b.max in
  if REPR.lt x min then { repr = min }
  else if REPR.gt x max then { repr = max }
  else { repr = x }

let add_sat (#b1: bounds) (#b2: bounds { Int.fits (b1.min + b2.min) REPR.n /\ Int.fits (b1.max + b2.max) REPR.n }) (x: t b1) (y: t b2): t b1 =
  let r = REPR.add x.repr y.repr in
  clamp r

// let div_underspec (a b: t min max): r: t { REPR.v b <> 0 ==> r = REPR.div a b } =
//   if b = 0uL then 0uL else REPR.div a b

// very under-specified rem: requires minimum bound to be 0 to avoid overflows like -32768/-1
let rem_underspec (#b: bounds { b.min == 0 }) (x y: t b): t b  =
  // refinement? { REPR.v y.repr <> 0 ==> REPR.v r.repr == REPR.v x.repr % REPR.v y.repr }
  if y.repr <> 0l then begin
    let r = REPR.rem x.repr y.repr in
    { repr = r }
  end else
    { repr = 0l }


let min (#b: bounds) (x y: t b): t b =
  if REPR.lt x.repr y.repr then x else y

let max (#b: bounds) (x y: t b): t b =
  if REPR.lt x.repr y.repr then y else x

#push-options "--split_queries always --fuel 1 --ifuel 0"


(* Bit-shifting power-of-two; pow2 and Int.pow2_n are not extractable to C. *)
let pow2_n (#b: bounds { b.min == 0 /\ b.max <= 30 }) (x: t b): t { min = 1; max = Int.pow2_n #REPR.n b.max } =
  let shift = Cast.int32_to_uint32 x.repr in
  Math.pow2_le_compat 30 (UInt32.v shift);
  Math.pow2_le_compat b.max (UInt32.v shift);
  let pow = REPR.shift_left 1l shift in
  { repr = pow }

#pop-options

let pow2_minus_one (#b: bounds { b.min == 0 /\ b.max <= 30 }) (x: t b): t { min = 0; max = Int.pow2_n #REPR.n b.max - 1 } =
  let pow = pow2_n x in
  { repr = REPR.sub pow.repr 1l }

let gt  (#b: bounds) (x y: t b): bool = REPR.gt  x.repr y.repr
let gte (#b: bounds) (x y: t b): bool = REPR.gte x.repr y.repr
let lt  (#b: bounds) (x y: t b): bool = REPR.lt  x.repr y.repr
let lte (#b: bounds) (x y: t b): bool = REPR.lte x.repr y.repr

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
