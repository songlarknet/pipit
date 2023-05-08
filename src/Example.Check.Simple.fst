(* Checking a simple example *)
module Example.Check.Simple

module Exp = Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = FStar.Tactics
module Sugar = Pipit.Sugar
open Sugar

let tac_nbe (): T.Tac unit = T.norm [primops; iota; delta; zeta; nbe]

(*
   count_when p =
     let rec count =
       (0 -> pre count) +
       (if p then 1 else 0)
*)
inline_for_extraction
let count_when (p: s bool): s int =
 rec' (fun count ->
   fby 0 count +^ (ite p z1 z0))

(* forall e. count_when false <= count_when e <= count_when true *)
let count_when_prop (e: s bool): s unit =
  let' (count_when ff) (fun count_when_false ->
  let' (count_when  e) (fun count_when_e ->
  let' (count_when tt) (fun count_when_true ->
  check' "0                <= count_when false" (z0               <=^ count_when_false) (
  check' "count_when false <= count_when e"     (count_when_false <=^ count_when_e) (
  check' "count_when e     <= count_when true"  (count_when_e     <=^ count_when_true) (
  pure ()))))))

let sys =
  system_of_exp (run1 count_when_prop)

let prove (fv: sem_freevars): Lemma (ensures induct1 (sys fv)) =
  assert (base_case (sys fv)) by (tac_nbe (); T.dump "base");
  assert (step_case (sys fv)) by (tac_nbe (); T.dump "step")
