module Pipit.Check.Example.TacX

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.ExpX

module T = FStar.Tactics


module Ck = Pipit.Check.Example

// always a => sometimes a
let example_GA_FA =
  osystem_of_exp (
    let open Ck in
    sofar x0 => once x0) 1

let example_GA_FA_base (): Lemma (ensures base_case' example_GA_FA) =
  assert (base_case' example_GA_FA) by tac_nbe ()

let example_GA_FA_step (): Lemma (ensures step_case' example_GA_FA) =
  assert (step_case' example_GA_FA) by tac_nbe ()

// sometimes a => always a (not true)
let example_FA_GA =
  osystem_of_exp (
    let open Ck in
    once x0 => sofar x0) 1

let example_FA_GA_base (): Lemma (ensures base_case' example_FA_GA) =
  assert (base_case' example_FA_GA) by tac_base ()

// this is not true so we can't prove it, but unfortunately we can't automatically disprove it
[@@expect_failure]
let example_FA_GA_step (): Lemma (ensures step_case' example_FA_GA) =
  assert (step_case' example_FA_GA) by tac_step ()

// always a => always (always a)
let example_GA_GGA =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    sofar a => sofar (sofar a))
    1

let example_GA_GGA_ok (): unit =
  assert (base_case' example_GA_GGA) by tac_nbe ();
  assert (step_case' example_GA_GGA) by tac_nbe ()

// sometimes a => not (always (not a))
let example_FA_nGnA =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    once a => Ck.not (sofar (Ck.not a)))
    1

let example_FA_nGnA_ok (): unit =
  assert (base_case' example_FA_nGnA) by tac_nbe ();
  assert (step_case' example_FA_nGnA) by tac_nbe ()

// always a /\ always (a => b) => always b
let example_GA_GAB__GB =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    let b = x1 in
    (sofar a /\ sofar (a => b)) => sofar b)
    2

let example_GA_GAB_GB_ok (): unit =
  assert (base_case' example_GA_GAB__GB) by tac_nbe ();
  assert (step_case' example_GA_GAB__GB) by tac_nbe ();
  ()

let example_FA_GAB__FB =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    let b = x1 in
    (sofar (a => b)) => (once a => once b))
    2

let example_GA_GAB_FB_ok (): Lemma (ensures base_case' example_FA_GAB__FB) =
  assert (base_case' example_FA_GAB__FB) by tac_nbe ();
  assert (step_case' example_FA_GAB__FB) by tac_nbe ()


let example_let =
  osystem_of_exp (
    let open Ck in
    let open Pipit.Exp.Base in
    XLet (once (XVar 0)) (
        let oa = XVar 0 in
        let a = XVar 1 in
        oa => once a))
    1

let example_let' (): Lemma (ensures base_case' example_let) =
  assert (base_case' example_let) by (tac_base (); T.dump "asdf");
  assert (step_case' example_let) by tac_nbe ()

let example_requires_invariant =
  osystem_of_exp (
    let open Ck in
    let open Pipit.Exp.Base in
    // a = 2 + 0
    XLet (once (XVar 2)) (
      // b = 1 + 1
      XLet (once (XVar 2)) (
        // c = 0 + 2
        XLet (once (XVar 2)) (
            let oc = XVar 0 in
            let ob = XVar 1 in
            let oa = XVar 2 in
            (oa /\ (oa => ob) /\ (ob => oc)) => oc))))
    3

let example_requires_invariant' (): Lemma (ensures base_case' example_requires_invariant) =
  assert (base_case' example_requires_invariant) by tac_nbe ();
  assert (step_case' example_requires_invariant) by tac_nbe ()
