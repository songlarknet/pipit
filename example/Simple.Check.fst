(* Checking a simple example *)
module Simple.Check

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics
open Pipit.Sugar

(*
   Count the number of times a predicate has been true.

   count_when p = count
    where
     count =
       (0 -> pre count) +
       (if p then 1 else 0)
*)
let count_when (p: bools): ints =
 rec' (fun count ->
   fby 0 count +^ (if_then_else p z1 z0))

(* forall e. count_when false <= count_when e <= count_when true *)
let count_when_prop (e: bools): bools =
  let' (count_when ff) (fun count_when_false ->
  let' (count_when  e) (fun count_when_e ->
  let' (count_when tt) (fun count_when_true ->
  check' "0                <= count_when false" (z0               <=^ count_when_false) (
  check' "count_when false <= count_when e"     (count_when_false <=^ count_when_e) (
  check' "count_when e     <= count_when true"  (count_when_e     <=^ count_when_true) (
  pure true))))))

let sys =
  assert_norm (Pipit.Exp.Causality.causal (run1 count_when_prop));
  system_of_exp (run1 count_when_prop)

let prove (): Lemma (ensures induct1 sys) =
  assert (base_case sys) by (T.norm_full ());
  assert (step_case sys) by (T.norm_full ())
