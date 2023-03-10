module Pipit.Check.Example.Manual

open Pipit.System.Base
open Pipit.System.Ind

module T = FStar.Tactics

// sofar e => once e
let example0_manual: system bool (bool * bool) bool =
  { init = (fun (sofar, once) -> (sofar = true) /\ (once = false));
    step = (fun i (sofar, once) (sofar', once') r ->
                sofar' = (sofar && i) /\
                once' = (once || i) /\
                r == (if sofar' then once' else true)
      ) }

let example0_manual' = system_map prop_of_bool example0_manual

let example0_ok_base (_: unit): Lemma (ensures base_case' example0_manual) =
  ()

let example0_ok_step (_: unit):
  Lemma (ensures step_case' example0_manual) =
  assert (step_case' example0_manual) by (T.compute (); T.dump "step_case");
  ()

let example0_ok_induct (_: unit):
  Lemma (ensures induct1 example0_manual') =
  // example0_ok_base ();
  // example0_ok_step ();
  ()



// the encoding from translating the expression has more existentials, so try adding them
// sofar e => once e
let exampleX_manual: system bool (bool * bool) bool =
  { init = (fun (sofar, once) -> (sofar = true) /\ (once = false));
    step = (fun i (sofar, once) (sofar', once') r ->
                exists ss oo.
                ss = (sofar && i) /\
                oo = (once || i) /\
                sofar' = ss /\
                once' = oo /\
                r == (if ss then oo else true)
      ) }

let exampleX_manual' = system_map prop_of_bool example0_manual

let exampleX_ok_base (_: unit): Lemma (ensures base_case' exampleX_manual) =
  ()

let exampleX_ok_step (_: unit):
  Lemma (ensures step_case' exampleX_manual) =
  assert (step_case' exampleX_manual) by (T.compute (); T.dump "step_case");
  ()
