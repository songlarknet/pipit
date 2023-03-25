(* Compiling a simple example to C.
   The program to translate is defined in Example.Check.Simple. *)
module Example.Compile.Pump

module Pump = Example.Check.Pump

module Exp = Pipit.Exp
module XX  = Pipit.Exec.Exp
module XL  = Pipit.Exec.LowStar

module Tac = FStar.Tactics
module B   = LowStar.Buffer
open FStar.HyperStack.ST

(* We will translate the "count_when" node with a variable as input.
   We do not want the expression's internal representation to show up in the
   C code, so we mark it as noextract. *)
noextract
let expr = (Pump.pump (Exp.XVar 0) (Exp.XVar 1) false)

(* Define the state type so it shows up as a type definition in the C code.
   The "postprocess_with" annotation ensures that the state_of_exp is inlined into the type and simplified to a regular type *)
[@@(Tac.postprocess_with XL.tac_extract)]
let state = XX.state_of_exp expr

type input = {
  estop_ok:  bool;
  level_low: bool;
}

type output = {
  pump_en:   bool;
  nok_stuck: bool;
}

(* Translate the expression to a transition system. *)
noextract
let system: Pipit.Exec.Base.exec (int * (int * unit)) state int =
  assert_norm (Exp.wf expr 2);
  XX.exec_of_exp expr 2

(* Define the reset function, which takes a pointer to the internal state and
   initialises it. *)
[@@(Tac.postprocess_with XL.tac_extract)]
let reset = XL.mk_reset system

(* Define the step function, which takes two input integers and a pointer to the
   internal state, and returns the result as a bitfield. We parse the bitfield
   before returning the values.
   *)
[@@(Tac.postprocess_with XL.tac_extract)]
let step (inp: input) (stref: B.pointer state): ST output
    (requires (fun h -> B.live h stref))
    (ensures (fun h _ h' -> B.live h' stref)) =
  let res = XL.mk_step system (Exp.value_of_bool inp.estop_ok, (Exp.value_of_bool inp.level_low, ())) stref in
  { pump_en = (res % Pump.pump_flag) <> 0; nok_stuck = (res % Pump.stuck_flag) <> 0 }
