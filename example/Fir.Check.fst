(* This is an example of an FIR filter. *)
module Fir.Check

open Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

// open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

module R = FStar.Real

type pos = r: R.real { R.(r >. 0.0R) }

let rec fir (coeffs: list R.real) (input: reals): reals =
  match coeffs with
  | [] -> zero
  | c :: coeffs' -> (input *^ const c) +^ fir coeffs' (fby 0.0R input)

let fir2 (input: reals): reals = fir [0.7R; 0.3R] input

let bibo2_body (n: pos) (signal: reals): bools =
  check "bibo" (sofar (abs signal <=^ const n) => (abs (fir2 signal) <=^ const n))

let bibo2 n: reals -> bools =
  let e = Check.exp_of_stream1 (bibo2_body n) in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Fir.Check"]);
  Check.stream_of_checked1 e

let fir3 (input: reals): reals = fir [0.7R; 0.2R; 0.1R] input

let bibo3_body (n: pos) (signal: reals): bools =
  check "bibo" (sofar (abs signal <=^ const n) => (abs (fir3 signal) <=^ const n))

let bibo3 n: reals -> bools =
  let e = Check.exp_of_stream1 (bibo3_body n) in
  assert (Check.system_induct_k 2 e) by (T.norm_full ["Fir.Check"]);
  Check.stream_of_checked1 e
