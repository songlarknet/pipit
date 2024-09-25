(* This is an example of an FIR filter. *)
module Fir.Check

open Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

// open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

let rec fir (coeffs: list pos) (input: ints): ints =
  match coeffs with
  | [] -> zero
  | c :: coeffs' -> (input *^ const c) +^ fir coeffs' (fby 0 input)

let fir2 (input: ints): ints = fir [7; 3] input

let bibo2_body (n: pos) (signal: ints): units =
  check "bibo" (sofar (abs signal <=^ const n) => (abs (fir2 signal) <=^ const n *^ const 10))

let bibo2 n: ints -> units =
  let e = Check.exp_of_stream1 (bibo2_body n) in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Fir.Check"]);
  Check.stream_of_checked1 e

let fir3 (input: ints): ints = fir [7; 2; 1] input

let bibo3_body (n: pos) (signal: ints): units =
  check "bibo" (sofar (abs signal <=^ const n) => (abs (fir3 signal) <=^ const n *^ const 10))

let bibo3 n: ints -> units =
  let e = Check.exp_of_stream1 (bibo3_body n) in
  assert (Check.system_induct_k 2 e) by (T.norm_full ["Fir.Check"]);
  Check.stream_of_checked1 e
