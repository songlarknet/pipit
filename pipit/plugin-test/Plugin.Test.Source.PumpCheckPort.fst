(* Experimental port of `Example.Pump.Check` to the new AST pipeline
   (`lift_ast_tac1`), without `#lang-pipit`. Some bindings need surface
   adjustments and a few are likely to fail on currently-unsupported
   features (tuple destructure in `controller`, etc.). *)
module Plugin.Test.Source.PumpCheckPort

module PPI = Pipit.Plugin.Interface
module PPL = Pipit.Plugin.Lift
open Pipit.Plugin.Interface
open Pipit.Source

(* ----- 1. min: arithmetic comparison + if-then-else ----- *)

[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let min (a b: int): int =
  if a <= b then a else b
%splice[] (PPL.lift_ast_tac1 "min")

(* ----- 2. once / sofar: non-function let rec → explicit rec' ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let once (p: bool): bool =
  rec' (fun r -> p || (false `fby` r))
%splice[] (PPL.lift_ast_tac1 "once")

[@@source_mode (ModeFun Stream true Stream)]
let sofar (p: bool): bool =
  rec' (fun r -> p && (true `fby` r))
%splice[] (PPL.lift_ast_tac1 "sofar")

(* ----- 3. top-level int constants ----- *)
let count_max: int = 65535
let settle_time: int = 1000
let stuck_time:  int = 6000
let max_flow:            int = 10
let level_low_threshold: int = 80
let max_level:           int = 100

(* ----- 4. countsecutive: rec' + ACallStream into min + check ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let countsecutive (p: bool): int =
  let count = rec' (fun count ->
    if p then min ((0 `fby` count) + 1) count_max else 0)
  in
  check (0 <= count);
  count
%splice[] (PPL.lift_ast_tac1 "countsecutive")

(* ----- 5. lastn / anyn: static-int arg mixed with stream-bool arg.
       This will exercise mixed-mode ACallStream. ----- *)

[@@source_mode (ModeFun Static true (ModeFun Stream true Stream))]
let lastn (n: int) (p: bool): bool =
  countsecutive p >= n
%splice[] (PPL.lift_ast_tac1 "lastn")

[@@source_mode (ModeFun Static true (ModeFun Stream true Stream))]
let anyn (n: int) (p: bool): bool =
  countsecutive (not p) < n
%splice[] (PPL.lift_ast_tac1 "anyn")

(* ----- 6. Exercise mixed-mode ACallStream into lastn (static int + stream bool) ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let lastn_caller (p: bool): bool =
  lastn settle_time p
%splice[] (PPL.lift_ast_tac1 "lastn_caller")

(* ----- 7. reservoir_model: rec' + ACallStream into min + static-coerced arg ----- *)

[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let reservoir_model (flow: int) (sol_en: bool): int =
  rec' (fun level ->
    (0 `fby` level) + (if sol_en then flow else min flow 0))
%splice[] (PPL.lift_ast_tac1 "reservoir_model")

(* ----- 8. spec_any_needs_extra_invariant_manual_cse: heavy chain ----- *)

[@@source_mode (ModeFun Stream true (ModeFun Stream true (ModeFun Stream true Stream)))]
let spec_any_needs_extra_invariant_manual_cse
    (flow: int) (estop level_low: bool): unit =
  let sol_try_c   = countsecutive (not estop && level_low) in
  let level_low_c = countsecutive level_low in
  let sol_try     = sol_try_c >= settle_time in
  let nok_stuck   = once (lastn stuck_time sol_try) in
  let sol_en      = sol_try && not nok_stuck in
  let level       = reservoir_model flow sol_en in
  check (sol_try_c <= level_low_c);
  check
    (sofar (abs flow < max_flow) ==>^
    (sofar (level > level_low_threshold ==>^ (level_low_c < settle_time)) ==>^
    (level < max_level)))
%splice[] (PPL.lift_ast_tac1 "spec_any_needs_extra_invariant_manual_cse")

(* ----- 9. controller_body: tuple-returning binding. Works: tuple
       construction in the return position lifts as `Mktuple2` prim
       (a plain APrim AppPureStream over `tuple2 bool bool`). ----- *)

[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let controller_body (estop level_low: bool): (bool & bool) =
  let sol_try   = lastn settle_time (not estop && level_low) in
  let nok_stuck = once (lastn stuck_time sol_try) in
  let sol_en    = sol_try && not nok_stuck in
  check (estop ==>^ not sol_en);
  check (not level_low ==>^ not sol_en);
  (sol_en, nok_stuck)
%splice[] (PPL.lift_ast_tac1 "controller_body")

(* ----- Not portable yet -----
   `controller` (tuple destructure on argument)
   `spec_body`  (let (sol_en, _) = controller_body ... — tuple destructure
                 on let binding)
   Both desugar to a `Tv_Match` with a `Mktuple2` constructor pattern;
   the AST pipeline currently only supports if-then-else
   (bool match). General constructor pattern matches need the
   clock-semantics work (see session notes / Pipit.Source.Ast.fst
   header). *)
