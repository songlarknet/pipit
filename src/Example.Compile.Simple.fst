(* Compiling a simple example to C.
   The program to translate is defined in Example.Check.Simple. *)
module Example.Compile.Simple

module Simple = Example.Check.Simple

module XX = Pipit.Exec.Exp
module XL = Pipit.Exec.LowStar

module Tac = FStar.Tactics

(* We will translate the "count_when" node with a variable as input.
   We do not want the expression's internal representation to show up in the
   C code, so we mark it as noextract. *)
noextract
let expr = (Simple.count_when (Pipit.Exp.XVar 0))

(* Define the state type so it shows up as a type definition in the C code.
   The "postprocess_with" annotation ensures that the state_of_exp is inlined into the type and simplified to a regular type *)
[@@(Tac.postprocess_with XL.tac_extract)]
let state = XX.state_of_exp expr

(* Translate the expression to a transition system. *)
noextract
let system: Pipit.Exec.Base.exec (int * unit) state int = XX.exec_of_exp expr 1

(* Define the reset function, which takes a pointer to the internal state and
   initialises it. *)
[@@(Tac.postprocess_with XL.tac_extract)]
let reset = XL.mk_reset system

(* Define the step function, which takes an input integer and a pointer to the
   internal state, and returns the result.
   The translation expects the input variables as a unit-terminated list of
   nested tuples, so we pass the input as (inp, ()) instead of just inp.
   The extraction is also a bit fragile, because it relies on the tac_extract
   tactic fully normalizing the step function. Unfortunately, when we pass a
   variable of type (int * unit) rather than a pair constructors (inp, ()), some
   functions are not totally normalized.
   *)
[@@(Tac.postprocess_with XL.tac_extract)]
let step (inp: int) = XL.mk_step system (inp, ())
