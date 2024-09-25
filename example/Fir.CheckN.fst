(* This is an example of proving semi-interesting things by mixing induction over lists with proofs about streams. *)
module Fir.CheckN

open Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

// open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

(* TODO move to ratio or fixed-point representation *)
let tint = Pipit.Prim.Vanilla.TInt

let bibo_rely = Check.exp_of_stream1 #_ #tint
  (fun i -> (const (-1)) <=^ i /\ i <=^ const 1)

let bibo_guar (mul: int) = Check.exp_of_stream2 #_ #tint #tint
  (fun r i -> r <=^ const mul)

type bibo_contract (mul: int) =
  Check.contract table [tint] tint
    bibo_rely
    (bibo_guar mul)

let r_abs (r: int): int =
  if r >= 0 then r else -r

let rec sum_abs (coeffs: list int) =
  match coeffs with
  | [] -> 0
  | c::cs' -> r_abs c + sum_abs cs'

#push-options "--split_queries always"

let rec fir (coeffs: list int):
  bibo_contract (sum_abs coeffs) =
  match coeffs with
  | [] ->
    let ret = Check.exp_of_stream1 (fun _ -> const 0) in

    assert (Check.contract_system_induct_k1' bibo_rely (bibo_guar 0) ret) by (T.norm_full ["Fir"]);
    Check.contract_of_exp1 _ _ ret
  | c :: coeffs' ->
    let fir': bibo_contract (sum_abs coeffs') = fir coeffs' in
    let ret = Check.exp_of_stream1 (fun input ->
      (input *^ const c) +^ Check.stream_of_contract1 fir' (fby 0 input)) in

    assert (sum_abs coeffs == r_abs c + sum_abs coeffs');
    assert (Check.contract_system_induct_k1' bibo_rely (bibo_guar (sum_abs coeffs)) ret) by (T.norm_full ["Fir"]);
    Check.contract_of_exp1 _ _ ret
