(* Compiling a simple example to C.
   The program to translate is defined in Pump.Check.fst. *)
module Pump.Extract

module Pump = Pump.Check

module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.LowStar

module Tac = FStar.Tactics

module SugarBase = Pipit.Sugar.Base
module Sugar = Pipit.Sugar.Vanilla

module PPV = Pipit.Prim.Vanilla

(* We will translate just the controller node with two input streams (estop and
   level). We do not want the expression's internal representation to show up in
   the C code, so we mark it as noextract.
   *)
noextract
let expr = SugarBase.exp_of_stream2 Pump.controller

(* Define the state type so it shows up as a type definition in the C code.
   The "postprocess_with" annotation ensures that the state_of_exp is inlined
   into the type and simplified to a regular type *)
[@@(Tac.postprocess_with XL.tac_extract)]
let state_opt = XX.state_of_exp_opt expr

[@@(Tac.postprocess_with XL.tac_extract)]
type state = XX.state_of_exp expr

type result = bool & bool

type input = {
  estop:     bool;
  level_low: bool;
}

(* Translate the expression to a transition system.
   Annotate with result type (bool & bool) so system is clearer. If we leave
   out the type annotation, then the generated KRML code may infer the result
   of the `step` function to be `any`, which breaks compilation.
*)
noextract
let system: Pipit.Exec.Exp.system (bool & (bool & unit)) state_opt result =
  assert_norm (XX.extractable expr);
  XX.exec_of_exp expr

(* Define the reset function, which takes a pointer to the internal state and
   initialises it. *)
[@@(Tac.postprocess_with XL.tac_extract)]
let reset = XL.mk_reset system

(* Define the step function, which takes two input booleans and a pointer to the
   internal state, and returns the result as a pair. *)
[@@(Tac.postprocess_with XL.tac_extract)]
let step (inp: input) = XL.mk_step system (inp.estop, (inp.level_low, ()))
