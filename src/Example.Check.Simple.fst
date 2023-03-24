(* Checking a simple example *)
module Example.Check.Simple

open Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = FStar.Tactics
module Sugar = Pipit.Sugar

let tac_nbe (): T.Tac unit = T.norm [primops; iota; delta; zeta; nbe]

(*
   count_when p =
     let rec count =
       (0 -> pre count) +
       (if p then 1 else 0)
*)
inline_for_extraction
let count_when (p: exp) =
 let open Sugar in
 mu' (
   let count = XVar 0 in
   let p' = lift' p in

   (z0 --> pre count) +^ (ite p' z1 z0))

(* forall e. count_when false <= count_when e <= count_when true *)
let count_when_prop =
  let open Sugar in
  system_of_exp (
    let' (count_when ff) (
      let' (count_when x0) (
        let' (count_when tt) (
          let count_when_false = x2 in
          let count_when_e = x1 in
          let count_when_true = x0 in
          count_when_false <=^ count_when_e /\ count_when_e <=^ count_when_true))))
    1

let count_when_prop_prove (): Lemma (ensures induct1' count_when_prop) =
  assert (base_case' count_when_prop) by tac_nbe ();
  assert (step_case' count_when_prop) by tac_nbe ()
