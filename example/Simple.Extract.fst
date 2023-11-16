(* Compiling a simple example to C.
   The program to translate is defined in Simple.Check.fst. *)
module Simple.Extract

module Simple = Simple.Check

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
[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Simple"]))]
noextract
let expr = SugarBase.exp_of_stream1 Simple.count_when

(* Define the state type so it shows up as a type definition in the C code.
   The "postprocess_with" annotation ensures that the state_of_exp is inlined
   into the type and simplified to a regular type *)
[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Simple"]))]
type state = XX.state_of_exp expr

type result = int

(* Translate the expression to a transition system.
   Annotate with input type (bool & unit) so system is clearer. If we leave
   out the type annotation, then the generated KRML code may infer the result
   of the `step` function to be `any`, which breaks compilation.
*)
// #push-options "--debug Simple.Extract --debug_level NBE"
[@@(Tac.postprocess_with (XL.tac_normalize_pure ["Simple"]))]
noextract
inline_for_extraction
let system: XX.esystem (bool & unit) int result =
  assert_norm (XX.extractable expr);
  XX.exec_of_exp expr


(* Define the reset function, which takes a pointer to the internal state and
   initialises it. *)
[@@(Tac.postprocess_with (XL.tac_extract ["Simple"]))]
let reset = XL.mk_reset system

(* Define the step function, which takes two input booleans and a pointer to the
   internal state, and returns the result as a pair. *)
[@@(Tac.postprocess_with (XL.tac_extract ["Simple"]))]
let step (inp: bool) = XL.mk_step system (inp, ())
