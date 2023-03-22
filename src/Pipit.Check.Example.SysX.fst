(* eXtended system examples *)
module Pipit.Check.Example.SysX

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.ExpX

module T = FStar.Tactics


module Sg = Pipit.Sugar

// always a => sometimes a
let example_GA_FA =
  osystem_of_exp (
    let open Sg in
    sofar x0 => once x0) 1

let example_GA_FA_base (): Lemma (ensures base_case' example_GA_FA) =
  assert (base_case' example_GA_FA) by tac_nbe ()

let example_GA_FA_step (): Lemma (ensures step_case' example_GA_FA) =
  assert (step_case' example_GA_FA) by tac_nbe ()

// sometimes a => always a (not true)
let example_FA_GA =
  osystem_of_exp (
    let open Sg in
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
    let open Sg in
    let a = x0 in
    sofar a => sofar (sofar a))
    1

let example_GA_GGA_ok (): unit =
  assert (base_case' example_GA_GGA) by tac_nbe ();
  assert (step_case' example_GA_GGA) by tac_nbe ()

// sometimes a => not (always (not a))
let example_FA_nGnA =
  osystem_of_exp (
    let open Sg in
    let a = x0 in
    once a => !(sofar !a))
    1

let example_FA_nGnA_ok (): unit =
  assert (base_case' example_FA_nGnA) by tac_nbe ();
  assert (step_case' example_FA_nGnA) by tac_nbe ()

// always a /\ always (a => b) => always b
let example_GA_GAB__GB =
  osystem_of_exp (
    let open Sg in
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
    let open Sg in
    let a = x0 in
    let b = x1 in
    (sofar (a => b)) => (once a => once b))
    2

let example_GA_GAB_FB_ok (): Lemma (ensures base_case' example_FA_GAB__FB) =
  assert (base_case' example_FA_GAB__FB) by tac_nbe ();
  assert (step_case' example_FA_GAB__FB) by tac_nbe ()


let example_let =
  osystem_of_exp (
    let open Sg in
    let' (once x0) (
        let oa = x0 in
        let a = x1 in
        oa => once a))
    1

let example_let' (): Lemma (ensures base_case' example_let) =
  assert (base_case' example_let) by (tac_base (); T.dump "asdf");
  assert (step_case' example_let) by tac_nbe ()

(* duplicate expressions - multiple instances of the same modal operator applied to the same arguments.
   this one is complex enough that induction alone won't get it without extra invariants:
   we need to tell it that the occurrences of `once` are the same.
  *)
let example_no_cse =
  osystem_of_exp (
    let open Sg in
    let c = x0 in
    let b = x1 in
    let a = x2 in
    (once a /\ (once a => once b) /\ (once b => once c)) => once c)
    3

let example_no_cse' (): Lemma (ensures base_case' example_no_cse) =
  assert (base_case' example_no_cse) by tac_nbe ()

(* the step case fails *)
[@@expect_failure]
let example_no_cse_step (): unit =
  assert (step_case' example_no_cse) by tac_nbe ()

(* common subexpression elimination lets it go through OK *)
let example_cse =
  osystem_of_exp (
    let open Sg in
    // a = 2 + 0
    let' (once x2) (
      // b = 1 + 1
      let' (once x2) (
        // c = 0 + 2
        let' (once x2) (
            let oc = x0 in
            let ob = x1 in
            let oa = x2 in
            (oa /\ (oa => ob) /\ (ob => oc)) => oc))))
    3

let example_cse' (): Lemma (ensures base_case' example_cse) =
  assert (base_case' example_cse) by tac_nbe ();
  assert (step_case' example_cse) by tac_nbe ()


(* count *)
let example_counts =
  let open Sg in
  osystem_of_exp (
  let' (countsecutive x0) (
    let c = x0 in
    z0 <=^ c /\ (!x1 => (c =^ z0) ))) 1

let example_counts' (): Lemma (ensures base_case' example_counts) =
  assert (base_case' example_counts) by tac_nbe ();
  assert (step_case' example_counts) by tac_nbe ()

(* count_when false <= count_when e <= count_when true *)
let example_counts_upper_bound =
  let open Sg in
  osystem_of_exp (
    let' (countsecutive x0) (
      let' (countsecutive tt) (
        let' (countsecutive ff) (
        let cX = x2 in let cT = x1 in let cF = x0 in
        cF =^ z0 /\ cF <=^ cX /\ cX <=^ cT)))) 1

let example_counts_upper' (): Lemma (ensures base_case' example_counts_upper_bound) =
  assert (base_case' example_counts_upper_bound) by tac_nbe ();
  assert (step_case' example_counts_upper_bound) by tac_nbe ()
