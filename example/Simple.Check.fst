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
  let' (count_when ff) (fun count_when_false ->
  let' (count_when  e) (fun count_when_e ->
  let' (count_when tt) (fun count_when_true ->
  check' "0                <= count_when false" (z0               <=^ count_when_false) (
  check' "count_when false <= count_when e"     (count_when_false <=^ count_when_e) (
  check' "count_when e     <= count_when true"  (count_when_e     <=^ count_when_true) (
  pure true))))))

let count_when_prop: bools -> bools =
  let e = Check.exp_of_stream1 count_when_prop_body in
  assert (Check.system_induct_k1 e) by (T.norm_full ());
  Check.stream_of_checked1 e

let sum_contract (i: ints): Base._contract Vanilla.table Vanilla.TInt = {
    rely = i >^ z0;
    guar = (fun sum -> sum >^ (0 `fby` sum));
    impl = rec' (fun sum -> (0 `fby` sum) +^ i);
  }

let sum: ints -> ints =
  let c = Check.contract_of_stream1 sum_contract in
  assert (Check.contract_system_induct_k1 c) by (T.norm_full ());
  Check.stream_of_contract1 c

let test_sum (i: ints) =
  let' (if_then_else (i >^ z0) i z1) (fun arg ->
  let' (sum arg) (fun sarg ->
  check' "sum is increasing" (sarg >^ (0 `fby` sarg))
    sarg
  ))

let test_sum_ =
  let e = Check.exp_of_stream1 test_sum in
  assert (Check.system_induct_k1 e) by (T.norm_full ());
  Check.stream_of_checked1 e
