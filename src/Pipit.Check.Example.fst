module Pipit.Check.Example

open Pipit.Exp.Base
open Pipit.System.Ind
module S = Pipit.System.Base

let tt = XVal true
let ff = XVal false

let x0 = XVar 0
let x1 = XVar 1
let x2 = XVar 2

let prim2 (p: prim2) (e1 e2: exp): exp = XPrim2 p e1 e2

let (/\) = prim2 And
let (\/) = prim2 Or
let (=>) = prim2 Implies
let (=?) = prim2 Eq

let not (e1: exp) = e1 =? ff

let pre (e: exp) = XPre e

let (-->) (e1 e2: exp) = XThen e1 e2

let mu (e: exp): exp = XMu e

let let' (e1 e2: exp): exp = XLet e1 e2

let lift' (e: exp) = Pipit.Exp.Subst.lift e 0

let sofar (e: exp): exp =
  mu (lift' e /\ pre x0)

let once (e: exp): exp =
  mu (lift' e \/ (ff --> pre x0))


let example0_ok (e: exp) =
  sofar e => once e

let example1_bad (e: exp) =
  once e => sofar e

module T = FStar.Tactics

let example0_ok_t = Pipit.System.Exp.system_of_exp (example0_ok x0) 1

let example0_ok_t' = Pipit.System.Base.system_map prop_of_bool example0_ok_t

let example0_ok_base (_: unit):
  Lemma (ensures base_case' example0_ok_t) =
  assert (base_case' example0_ok_t) by (T.compute (); T.dump "base_case");
  ()

let example0_ok_step (_: unit):
  Lemma (ensures step_case' example0_ok_t) =
  assert (step_case' example0_ok_t) by (T.compute (); T.dump "step_case");
  admit ()

let example0_ok_induct (_: unit):
  Lemma (ensures induct1 example0_ok_t') =
  example0_ok_base ();
  example0_ok_step ();
  ()

let example0_ok_check ():
  Lemma (ensures exp_for_all (example0_ok x0) 1) =
  let e = example0_ok x0 in
  // assert (exp_valid e 1) by T.compute ();
  example0_ok_induct ();
  // assert (base_case example0_ok_t') by (T.compute (); T.dump "base_case");
  // assert (step_case example0_ok_t') by (T.compute (); T.dump "step_case");
  induct1_exp #1 e;
  // assert (exp_for_all (example0_ok x0) 1);
  ()

let example1_bad_t = Pipit.System.Exp.system_of_exp (example1_bad x0) 1

let example1_bad_t' = Pipit.System.Base.system_map prop_of_bool example1_bad_t

let example1_bad_base ():
  Lemma (ensures (base_case example1_bad_t')) =
  assert (base_case example1_bad_t') by (T.compute (); T.dump "base_case");
  ()

// let example1_bad_bmc2 ():
//   Lemma (ensures ~ (bmc2 example1_bad_t')) =
//   assert (~ (bmc2 example1_bad_t')) by (T.compute (); T.dump "bmc2");
//   ()

// let example1_bad_step ():
//   Lemma (ensures ~ (bmc2 example1_bad_t')) = ()
