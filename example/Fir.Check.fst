module Fir.Check

open Pipit.Sugar

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics

type sample = int

let rec fir (coeffs: list sample) (sig: s sample): s sample =
  match coeffs with
  | [] -> z0
  | c :: coeffs' -> (sig *^ pure c) +^ fir coeffs' (fby 0 sig)

let fir2_contract (n: nat) (cfg: list sample) (signal: s sample): s unit =
  let out = fir cfg signal in
  let ok  = signal <=^ z n in
  check "contract"
    (sofar ok => (out <=^ z (op_Multiply n 10)))

let fir2_prop n =
  assert_norm (Pipit.Exp.Causality.causal (run1 (fir2_contract n [8; 2])));
  system_of_exp (run1 (fir2_contract n [8; 2]))

let fir3_contract (cfg: list sample) (signal: s sample): s unit =
  let out = fir cfg signal in
  let ok  = signal <=^ z 100 in
  check "contract"
    (sofar ok => (out <=^ z 1000))

let fir3_prop =
  assert_norm (Pipit.Exp.Causality.causal (run1 (fir3_contract [7; 2; 1])));
  system_of_exp (run1 (fir3_contract [7; 2; 1]))

// #push-options "--tactic_trace_d 1"
let fir_prop_prove (n: nat): Lemma (ensures induct1 (fir2_prop n)) =
  assert (base_case (fir2_prop n)) by (T.norm_full (); T.pipit_simplify (); T.norm_full (); T.dump "base");
  assert (step_case (fir2_prop n)) by (T.norm_full (); T.pipit_simplify (); T.norm_full (); T.dump "step");
  ()

#push-options "--tactic_trace_d 1"
let fir3_prop_prove (): Lemma (induct1 fir3_prop) =
  // assert (base_case (fir3_prop fv)) by (tac_nbe (); tac_intros_smash (); tac_nbe (); T.dump "base");
  assert (step_case_k 2 fir3_prop) by (T.pipit_simplify' 10; T.dump "step");
  admit ()
