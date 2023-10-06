(* This is an example of proving interesting things by mixing induction over lists with proofs about streams. *)
module Fir.CheckN

open Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

// open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

module R = FStar.Real

let treal = Pipit.Prim.Vanilla.TReal

type fir_contract (mul: R.real) =
  Check.contract table [treal] treal
    (Check.exp_of_stream1 (fun i -> (const (R.of_int (-1))) <=^ i /\ i <=^ r1))
    (Check.exp_of_stream2 (fun r i -> r <=^ const mul))

// type fir_contract' (mul: list R.real) =
//   Check.contract1 table [treal] treal
//     (fun i -> abs i <=^ r1)
//     (fun i r -> abs r <=^ const mul)

let r_abs (r: R.real): R.real =
  R.(if r >=. zero then r else (zero -. r))

let rec sum_abs (coeffs: list R.real) =
  match coeffs with
  | [] -> R.zero
  | c::cs' -> R.(r_abs c +. sum_abs cs')

#push-options "--split_queries always"


#push-options "--print_full_names"
let rec fir_body (coeffs: list R.real):
  fir_contract (sum_abs coeffs) =
  let r = (Check.exp_of_stream1 (fun i -> (const (R.of_int (-1))) <=^ i /\ i <=^ r1)) in
  let g = (Check.exp_of_stream2 (fun r i -> r <=^ const (sum_abs coeffs))) in
  match coeffs with
  | [] ->
    let e = Check.exp_of_stream1 (fun _ -> zero) in
    assert (Check.contract_system_induct_k1' r g e) by (T.norm_full ());
    Check.contract_of_exp1 r g e
  | c :: coeffs' ->
    let e = Check.exp_of_stream1 (fun input ->
      let fir' = Check.stream_of_contract1 (fir_body coeffs') (fby 0.0R input) in
      (input *^ const c) +^ fir') in
    assert (Check.contract_system_induct_k1' r g e) by (T.norm_full ());
    Check.contract_of_exp1 r g e
