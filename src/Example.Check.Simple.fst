(* Checking a simple example *)
module Example.Check.Simple

module Exp = Pipit.Exp.Base

// open Pipit.System.Base
// open Pipit.System.Ind
// open Pipit.System.Exp

module T = FStar.Tactics
module Sugar = Pipit.SugarX3
open Sugar

let tac_nbe (): T.Tac unit = T.norm [primops; iota; delta; zeta; nbe]

(*
   count_when p =
     let rec count =
       (0 -> pre count) +
       (if p then 1 else 0)
*)
inline_for_extraction
let count_when (p: stream bool): Stream (stream int) =
 rec' (fun count ->
   fby 0 count +^ (ite p z1 z0))

(* forall e. count_when false <= count_when e <= count_when true *)
let count_when_prop (e: stream bool): Stream (stream unit) =
  let' (count_when ff) (fun count_when_false ->
  let' (count_when e) (fun count_when_e ->
  let' (count_when tt) (fun count_when_true ->
  check' "count_when false <= count_when e" (count_when_false <=^ count_when_e) (
  check' "cwe<=cwt" (count_when_e <=^ count_when_true) (
  pure ())))))

let run (e: unit -> Stream 'a) : 'a =
  let (a, _) = reify (e ()) { fresh = 0 } in
  a


let sdf (): Stream unit =
  let xe = run (fun _ -> count_when_prop tt) in
  assert (xe == (pure ())) by (T.norm [primops; iota; delta]; T.norm [nbe]; T.dump "")
  // by (tac_nbe (); T.dump "")


//   let open Sugar in
//   system_of_exp (
//     let' (count_when ff) (
//       let' (count_when x0) (
//         let' (count_when tt) (
//           let count_when_false = x2 in
//           let count_when_e = x1 in
//           let count_when_true = x0 in
//           count_when_false <=^ count_when_e /\ count_when_e <=^ count_when_true))))
//     1

// let count_when_prop_prove (): Lemma (ensures induct1' count_when_prop) =
//   assert (base_case' count_when_prop) by tac_nbe ();
//   assert (step_case' count_when_prop) by tac_nbe ()
