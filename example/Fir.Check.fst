(* This is an example of an FIR filter. *)
module Fir.Check

open Pipit.Sugar

// open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

module R = FStar.Real

type pos = r: R.real { R.(r >. 0.0R) }

let rec fir (coeffs: list R.real) (input: reals): reals =
  match coeffs with
  | [] -> zero
  | c :: coeffs' -> (input *^ pure c) +^ fir coeffs' (fby 0.0R input)

let fir2 (input: reals): reals = fir [0.7R; 0.3R] input

let bibo2 (n: pos) (signal: reals): s bool =
  check "bibo" (sofar (abs signal <=^ pure n) => (abs (fir2 signal) <=^ pure n))

let bibo2' n =
  assert_norm (Pipit.Exp.Causality.causal (run1 (bibo2 n)));
  system_of_exp (run1 (bibo2 n))

let proof2 (n: pos): Lemma (ensures induct1 (bibo2' n)) =
  assert (base_case (bibo2' n)) by (T.pipit_simplify ());
  assert (step_case (bibo2' n)) by (T.pipit_simplify ());
  ()

let fir3 (input: reals): reals = fir [0.7R; 0.2R; 0.1R] input

let bibo3 (n: pos) (signal: reals): s bool =
  check "bibo" (sofar (abs signal <=^ pure n) => (abs (fir3 signal) <=^ pure n))

let bibo3' n =
  assert_norm (Pipit.Exp.Causality.causal (run1 (bibo3 n)));
  system_of_exp (run1 (bibo3 n))

let proof3 (n: pos): Lemma (ensures induct_k 2 (bibo3' n)) =
  assert (base_case_k 2 (bibo3' n)) by (T.pipit_simplify ());
  assert (step_case_k 2 (bibo3' n)) by (T.pipit_simplify ());
  ()

