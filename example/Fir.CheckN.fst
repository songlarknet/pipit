(* This is an example of proving semi-interesting things by mixing induction over lists with proofs about streams. *)
module Fir.CheckN

open Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

// open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

module R = FStar.Real

let treal = Pipit.Prim.Vanilla.TReal

let bibo_rely = Check.exp_of_stream1 #_ #treal
  (fun i -> (const (R.of_int (-1))) <=^ i /\ i <=^ r1)

let bibo_guar (mul: R.real) = Check.exp_of_stream2 #_ #treal #treal
  (fun r i -> r <=^ const mul)

type bibo_contract (mul: R.real) =
  Check.contract table [treal] treal
    bibo_rely
    (bibo_guar mul)

let r_abs (r: R.real): R.real =
  R.(if r >=. zero then r else (zero -. r))

let rec sum_abs (coeffs: list R.real) =
  match coeffs with
  | [] -> R.zero
  | c::cs' -> R.(r_abs c +. sum_abs cs')

#push-options "--split_queries always"

let rec fir (coeffs: list R.real):
  bibo_contract (sum_abs coeffs) =
  match coeffs with
  | [] ->
    let ret = Check.exp_of_stream1 (fun _ -> const 0.0R) in

    assert (Check.contract_system_induct_k1' bibo_rely (bibo_guar 0.0R) ret) by (T.norm_full ["Fir"]);
    Check.contract_of_exp1 _ _ ret
  | c :: coeffs' ->
    let fir': bibo_contract (sum_abs coeffs') = fir coeffs' in
    let ret = Check.exp_of_stream1 (fun input ->
      (input *^ const c) +^ Check.stream_of_contract1 fir' (fby 0.0R input)) in

    assert R.(sum_abs coeffs == r_abs c +. sum_abs coeffs');
    assert (Check.contract_system_induct_k1' bibo_rely (bibo_guar (sum_abs coeffs)) ret) by (T.norm_full ["Fir"]);
    Check.contract_of_exp1 _ _ ret
