(* Experimental port of `Example.Fir.Check` to the new AST pipeline
   (`lift_ast_tac1`), without `#lang-pipit`. *)
module Plugin.Test.Source.FirCheckPort

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
open Pipit.Plugin.Interface
open Pipit.Source

(* ----- sofar: non-function let rec → explicit rec' ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let sofar (p: bool): bool =
  rec' (fun r -> p && (true `fby` r))
%splice[] (PPL.lift_ast_tac1 "sofar")

(* ----- fir2: two-tap FIR filter (arithmetic + fby) ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let fir2 (input: int): int =
  input * 7 + (0 `fby` input) * 3
%splice[] (PPL.lift_ast_tac1 "fir2")

(* ----- bound: plain top-level int constant referenced from a binding ----- *)
let bound: int = 100

(* ----- bibo2: ACallStream into sofar/fir2, abs, ==>^, bound reference ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let bibo2 (signal: int): unit =
  check
    (sofar (abs signal <= bound) ==>^
    (abs (fir2 signal) <= bound * 10))
%splice[] (PPL.lift_ast_tac1 "bibo2")
