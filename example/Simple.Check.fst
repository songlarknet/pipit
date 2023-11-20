(* Checking a simple example *)
module Simple.Check

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

open Pipit.Sugar.Vanilla
module Base = Pipit.Sugar.Base
module Check = Pipit.Sugar.Check

module Vanilla = Pipit.Prim.Vanilla

(*
   Count the number of times a predicate has been true.

   count_when p = count
    where
     count =
       (0 -> pre count) +
       (if p then 1 else 0)
*)
let count_when (p: bools): ints =
 rec' (fun count ->
   fby 0 count +^ (if_then_else p z1 z0))

(* forall e. count_when false <= count_when e <= count_when true *)
let count_when_prop_body (e: bools): bools =
  let^ count_when_false = count_when ff in
  let^ count_when_e     = count_when e  in
  let^ count_when_true  = count_when tt in
  check "0                <= count_when false" (z0               <=^ count_when_false);^
  check "count_when false <= count_when e"     (count_when_false <=^ count_when_e);^
  check "count_when e     <= count_when true"  (count_when_e     <=^ count_when_true)

let count_when_prop: bools -> bools =
  let e = Check.exp_of_stream1 count_when_prop_body in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Simple"]);
  Check.stream_of_checked1 e

type sum_contract = Check.contract Vanilla.table [Vanilla.TInt] Vanilla.TInt
  (Check.exp_of_stream1 (fun i -> i >^ z0))
  (Check.exp_of_stream2 (fun sum i -> sum >^ (0 `fby` sum)))

let sum: sum_contract =
  let r = (Check.exp_of_stream1 (fun i -> i >^ z0)) in
  let g = (Check.exp_of_stream2 (fun sum i -> sum >^ (0 `fby` sum))) in
  let e = Check.exp_of_stream1 (fun i ->
    rec' (fun sum -> (0 `fby` sum) +^ i)
  ) in
  assert (Check.contract_system_induct_k1' r g e) by (T.norm_full ["Simple"]);
  Check.contract_of_exp1 r g e

let test_sum (i: ints) =
  let^ arg  = if_then_else (i >^ z0) i z1 in
  let^ sarg = Check.stream_of_contract1 sum arg in
  check "sum is increasing" (sarg >^ (0 `fby` sarg))

let test_sum_ =
  let e = Check.exp_of_stream1 test_sum in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Simple"]);
  Check.stream_of_checked1 e

(* https://github.com/kind2-mc/cocospec_tcm_experiments/blob/master/systems/helpers.lus#L168 *)
let times_guarantee (x y z: ints) =
  let^ abs_x = abs x in
  let^ abs_y = abs y in
  let^ abs_z = abs z in
  // Neutral
  ((z =^ y) =^ ((x =^ z1) \/ (y =^ z0))) /\
  ((z =^ x) =^ ((y =^ z1) \/ (x =^ z0))) /\
  // Absorbing
  ((z =^ z0) =^ ((x =^ z0) \/ (y =^ z0))) /\
  // Sign
  ((z >^ z0) =^ (
    ((x >^ z0) /\ (y >^ z0)) \/
    ((x <^ z0) /\ (y <^ z0)))) /\
  ((z <^ z0) =^ (
    ((x >^ z0) /\ (y <^ z0)) \/
    ((x <^ z0) /\ (y >^ z0)))) /\
  // Loose proportionality
  ((abs_z >=^ abs_y) =^ ((abs_x >=^ z1) \/ (y =^ z0))) /\
  ((abs_z >=^ abs_x) =^ ((abs_y >=^ z1) \/ (x =^ z0))) /\
  ((abs_z <=^ abs_y) =^ ((abs_x <=^ z1) \/ (y =^ z0))) /\
  ((abs_z <=^ abs_x) =^ ((abs_y <=^ z1) \/ (x =^ z0)))

//TODO:EXAMPLES more contract examples
// let times_contract (x y: ints): Base._contract Vanilla.table Vanilla.TInt = {
//     rely = tt;
//     guar = times_guarantee x y;
//     impl = x *^ y;
//   }

// let times_abstraction: ints -> ints -> ints =
//   let c = Check.contract_of_stream2 times_contract in
//   assert (Check.contract_system_induct_k1 c) by (T.norm_full ["Simple"]);
//   Check.stream_of_contract2 c
