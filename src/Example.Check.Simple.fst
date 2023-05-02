(* Checking a simple example *)
module Example.Check.Simple

module Exp = Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = FStar.Tactics
module Sugar = Pipit.SugarX4
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
  let' (count_when e) (fun count_when_e ->
  let' (count_when tt) (fun count_when_true ->
  check' "count_when false <= count_when e" (count_when_false <=^ count_when_e) (
  check' "cwe<=cwt" (count_when_e <=^ count_when_true) (
  pure ())))))

let run (e: s 'a) : Exp.exp [] 'a =
  let (a, _) = e { fresh = 0 } in
  a

let count (): s int =
  rec' (fun count -> fby 0 count +^ z1)

let count_when__0_prop (e: s bool): s unit =
  check' "0 <= count_when e" (z0 <=^ z1) (pure ())


let sys =
  system_of_exp (run (count_when__0_prop ff))

// #push-options "--print_full_names --print_bound_var_types"
// let prove (fv: sem_freevars): Lemma (ensures base_case (sys fv)) =
//   assert (base_case (sys fv)) by (T.norm [primops; iota; delta; zeta; nbe]; T.dump "")
//   // assert (base_case (sys fv)) by (tac_nbe (); T.dump "")



// let doit (): unit =
//   let xe = run (count_when_prop (fresh bool)) in

//   assert (xe == Exp.XVal ()) by (T.norm [primops; iota; delta; zeta; nbe]; T.norm [delta_fully ["Pipit.SugarX3.STREAM?.reflect"]]; T.dump "")
//   // by (tac_nbe (); T.dump "")


let sdf (): unit =
  let xe = run z1 in
  let xy = run z1 in
  assert (xe == xy) by (T.norm [primops; iota; delta; nbe]; T.dump "")
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
