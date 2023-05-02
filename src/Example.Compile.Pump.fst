(* Compiling a simple example to C.
   The program to translate is defined in Example.Check.Pump. *)
module Example.Compile.Pump

module Pump = Example.Check.Pump

module Exp = Pipit.Exp
module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.LowStar

module Tac = FStar.Tactics
module B   = LowStar.Buffer
open FStar.HyperStack.ST

module Sugar = Pipit.SugarX4

(* We will translate the controller node with variables as input.
   We do not want the expression's internal representation to show up in the
   C code, so we mark it as noextract. *)
noextract
let expr = Sugar.run2 Pump.controller'

(* Define the state type so it shows up as a type definition in the C code.
   The "postprocess_with" annotation ensures that the state_of_exp is inlined into the type and simplified to a regular type *)
[@@(Tac.postprocess_with XL.tac_extract)]
let state = XX.state_of_exp expr

type input = {
  estop:     bool;
  level_low: bool;
}

(* Translate the expression to a transition system. *)
noextract
let system: Pipit.Exec.Exp.xexec expr =
  // assert_norm (Exp.wf expr 2);
  assert_norm (XX.extractable expr);
  XX.exec_of_exp expr

(* Define the reset function, which takes a pointer to the internal state and
   initialises it. *)
[@@(Tac.postprocess_with XL.tac_extract)]
let reset = XL.mk_reset system

(* Define the step function, which takes two input integers and a pointer to the
   internal state, and returns the result as a bitfield. We parse the bitfield
   before returning the values.
   *)

// [@@(Tac.postprocess_with XL.tac_extract)]
// let step (inp: input) (stref: B.pointer state): ST output
//     (requires (fun h -> B.live h stref))
//     (ensures (fun h _ h' -> B.live h' stref)) =
//   let res = XL.mk_step system (inp.estop, (inp.level_low, ())) stref in
//   admit ()
//   { sol_en = has_bit res Pump.solenoid_flag; nok_stuck = has_bit res Pump.stuck_flag }

[@@(Tac.postprocess_with XL.tac_extract)]
let step (inp: input) = XL.mk_step system (inp.estop, (inp.level_low, ()))

// let step' (inp: input) (stref: B.pointer state): ST _
//     (requires (fun h -> B.live h stref))
//     (ensures (fun h _ h' -> B.live h' stref)) =
//   step inp stref
