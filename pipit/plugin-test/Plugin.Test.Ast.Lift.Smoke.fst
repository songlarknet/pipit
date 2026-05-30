(* End-to-end smoke test for the new AST-based lift pipeline.

   `Pipit.Plugin.Lift.lift_ast_tac1` parses a source binding into
   `Pipit.Source.Ast.ast`, then lowers it via `Pipit.Source.Ast.Lower`
   to a core expression term. These tests verify that simple source
   programs make it all the way through to a well-typed `__core_*`
   sigelt. *)
module Plugin.Test.Ast.Lift.Smoke

open Pipit.Source

module PPL = Pipit.Plugin.Lift

(* ----- 1. integer literal stream ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let eg_const (x: int) : int = 0
%splice[] (PPL.lift_ast_tac1 "eg_const")

(* ----- 2. parameter reference ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let eg_id (x: int) : int = x
%splice[] (PPL.lift_ast_tac1 "eg_id")

(* ----- 3. fby with parameter tail ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let eg_fby (x: int) = 0 `fby` x
%splice[] (PPL.lift_ast_tac1 "eg_fby")

(* ----- 4. let-stream ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let eg_let_stream (x: int) =
  let y = 0 `fby` x in
  y
%splice[] (PPL.lift_ast_tac1 "eg_let_stream")

(* ----- 5. rec' producing an `AMu` ----- *)

(* Simplest fixpoint that doesn't need arithmetic primitives. Semantics:
   the stream `s` satisfying `s = 0 fby s`, i.e. constantly 0. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_rec_const (x: int) =
  rec' (fun n -> 0 `fby` n)
%splice[] (PPL.lift_ast_tac1 "eg_rec_const")

(* `rec'` bound via `let` — should desugar to `ALet ... (AMu ...) cont`
   via the AST `AVar`/`ALet` shape. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_let_rec_const (x: int) =
  let c = rec' (fun n -> 0 `fby` n) in
  c
%splice[] (PPL.lift_ast_tac1 "eg_let_rec_const")

(* ----- 7. arithmetic primitives ----- *)

(* `x + 1` — `op_Addition` lifted as `APrim AppPureStream`; the literal
   `1` is `ALit` (Static) that lowers to `XVal` in stream context. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_add_lit (x: int): int = x + 1
%splice[] (PPL.lift_ast_tac1 "eg_add_lit")

(* `x + x` — both operands are streams. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_add_xx (x: int): int = x + x
%splice[] (PPL.lift_ast_tac1 "eg_add_xx")

(* `0 `fby` (x + 1)` — combines `AFby` with `APrim AppPureStream`. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_fby_inc (x: int): int = 0 `fby` (x + 1)
%splice[] (PPL.lift_ast_tac1 "eg_fby_inc")

(* Pure counter: `rec' (fun n -> 0 `fby` (n + 1))`. Exercises
   `AMu` + `AFby` + `APrim AppPureStream` together. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_counter (x: int): int =
  rec' (fun n -> 0 `fby` (n + 1))
%splice[] (PPL.lift_ast_tac1 "eg_counter")

(* ----- 8. check ----- *)

(* `check` on a bool stream parameter. Exercises the `ACheck` path
   end-to-end: `lift_app_check` recognises `Pipit.Source.check`, Lower
   emits `XCheck`. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_check_var (x: bool): unit = check x
%splice[] (PPL.lift_ast_tac1 "eg_check_var")

(* ----- 9. comparison / bool primitives ----- *)

(* `x > 0` — `op_GreaterThan` lifted as `APrim AppPureStream`,
   returns `bool` stream. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_gt_lit (x: int): bool = x > 0
%splice[] (PPL.lift_ast_tac1 "eg_gt_lit")

(* `check (x > 0)` — the canonical safety check; combines `ACheck`,
   `APrim` and `ALit`. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_check_gt (x: int): unit = check (x > 0)
%splice[] (PPL.lift_ast_tac1 "eg_check_gt")

(* `x && y` — boolean conjunction across two stream parameters. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let eg_and (x y: bool): bool = x && y
%splice[] (PPL.lift_ast_tac1 "eg_and")

(* `x || y` — boolean disjunction. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let eg_or (x y: bool): bool = x || y
%splice[] (PPL.lift_ast_tac1 "eg_or")

(* `0 - x` — subtraction, exercises another arithmetic primitive
   shape with the literal on the left. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_neg (x: int): int = 0 - x
%splice[] (PPL.lift_ast_tac1 "eg_neg")

(* ----- 10. record projectors via derive_has_stream ----- *)

(* Record with a manually spliced `has_stream point` instance, so it
   has an in-scope instance at splice time. (The smoke test is not a
   `#lang-pipit` module, so the `[@@derive_has_stream]` attribute is
   not honoured automatically — we splice explicitly here.) *)
type point = { px: int; py: int; }
%splice[has_stream_point] (Pipit.Prim.HasStream.Derive.derive_has_stream "point")

(* Field projection `p.px` desugars to `Mkpoint?.px p`, an `APrim
   AppPureStream` over the projector function. Exercises that primitive
   recognition + `has_stream point` resolution at the splice site. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_proj_px (p: point): int = p.px
%splice[] (PPL.lift_ast_tac1 "eg_proj_px")

(* `p.px + p.py` — two projectors plus arithmetic. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_proj_sum (p: point): int = p.px + p.py
%splice[] (PPL.lift_ast_tac1 "eg_proj_sum")

(* ----- 11. if-then-else via p'select ----- *)

(* `if b then 1 else 0` — bool scrutinee, literal branches. The match
   shape `Tv_Match cond [(C_True, t); (C_False, f)]` is recognised
   and lowered to `APrim AppPureStream` over
   `PipitRuntime.Prim.p'select #int`. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_ite_lit (b: bool): int = if b then 1 else 0
%splice[] (PPL.lift_ast_tac1 "eg_ite_lit")

(* `if x > 0 then x else 0` — scrutinee is itself a stream-bool
   computed by `op_GreaterThan`; `then`-branch is the input stream. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_ite_pos (x: int): int = if x > 0 then x else 0
%splice[] (PPL.lift_ast_tac1 "eg_ite_pos")

(* `if b then x else y` — two stream arguments selected by a bool. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true (ModeFun Stream true Stream)))]
let eg_ite_xy (b: bool) (x y: int): int = if b then x else y
%splice[] (PPL.lift_ast_tac1 "eg_ite_xy")

(* `0 \`fby\` (if x > 0 then x else 0)` — combines `AFby` with `p'select`. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_fby_ite (x: int): int = 0 `fby` (if x > 0 then x else 0)
%splice[] (PPL.lift_ast_tac1 "eg_fby_ite")

(* ----- 12. ACallStream: calls into other lifted bindings ----- *)

(* `eg_callee_id x = x` — trivial callee. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_callee_id (x: int): int = x
%splice[] (PPL.lift_ast_tac1 "eg_callee_id")

(* `eg_caller_id x = eg_callee_id x` — single-arg call. Exercises the
   `XLet t1 (lower x) (weaken caller_ctx eg_callee_id_core)` shape. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_caller_id (x: int): int = eg_callee_id x
%splice[] (PPL.lift_ast_tac1 "eg_caller_id")

(* `eg_callee_add x y = x + y` — two-arg stream callee. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let eg_callee_add (x: int) (y: int): int = x + y
%splice[] (PPL.lift_ast_tac1 "eg_callee_add")

(* `eg_caller_add x y = eg_callee_add x y` — exercises the multi-arg
   XLet chain with caller variables that need to be shifted under the
   intermediate XLets. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let eg_caller_add (x: int) (y: int): int = eg_callee_add x y
%splice[] (PPL.lift_ast_tac1 "eg_caller_add")

(* `eg_caller_add_swap x y = eg_callee_add y x` — same as above but
   with swapped argument order, so caller-side indexes differ. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let eg_caller_add_swap (x: int) (y: int): int = eg_callee_add y x
%splice[] (PPL.lift_ast_tac1 "eg_caller_add_swap")

(* `eg_caller_fby x = 0 \`fby\` eg_callee_id x` — combines a fby with a
   stream-aware call. *)
[@@source_mode (ModeFun Stream true Stream)]
let eg_caller_fby (x: int): int = 0 `fby` eg_callee_id x
%splice[] (PPL.lift_ast_tac1 "eg_caller_fby")
