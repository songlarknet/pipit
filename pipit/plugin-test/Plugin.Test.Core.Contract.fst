(* Manual contract example -- hand-written approximation of what the
   plugin would generate for a user-supplied contract.

   See doc/roadmap/v1-source-followups.md for design context.

   ===== Contract shape =====

   A contract bundles three source-level pieces:

     rely:  stream a -> ... -> stream bool        precondition on inputs
     guar:  stream a -> ... -> stream r -> stream bool   postcondition on output
     body:  stream a -> ... -> stream r           implementation

   In the core IR they meet at an XContract node:

     XContract status (rely: exp t c propty)
                      (guar: exp t (a :: c) propty)
                      (impl: exp t c a)
                    : exp t c a

   with `a` the body's return type and `c` the body's input context.
   Note that `guar`'s context has the result variable at de-Bruijn 0
   (innermost), so under our "last-param == innermost" source
   convention the user writes `guar` with the result variable as its
   LAST parameter (the body's inputs come first).

   ===== Plugin output per contract =====

   For every user-supplied contract the plugin would generate three
   source defs and several splices:

     <rely>            -- user-supplied source binding
     <guar>            -- user-supplied source binding
     <body>            -- user-supplied source binding

     <rely>_core       via lift_ast_tac1 "<rely>"
     <guar>_core       via lift_ast_tac1 "<guar>"
     <body>_core       via lift_ast_tac1 "<body>"
     <body>_contract   wraps the three cores in XContract, optionally
                       via bless_contract if a proof attribute
                       (e.g. [@@proof_induct1]) is present.

   No special contract-aware lifting tactic is needed. Each of the
   three source defs is just a plain function and lifts identically
   to any other source binding via `lift_ast_tac1`. The
   contract-specific work is entirely in the assembly step (proof
   discharge + XContract wrap), which is a pure core-IR operation.

   The proof stage will start out optional (only when
   [@@proof_induct1] is present). Without a proof, the assembled
   binding stays at `XContract PSUnknown` (today's "unblessed"
   shape). A future [@@proof_admit] would `admit ()` the proof
   premises before calling `bless_contract`, giving an unverified
   "blessed" contract for staging.

   ===== This file =====

   Hand-written example of the assembly for one tiny contract:

     body x = x + 1
     rely x = x > 0
     guar x r = r > 0

   The three source defs are plain `[@@source_mode ...]` bindings (we
   could equivalently use #lang-pipit). Each is followed by an
   explicit `%splice[] (PPL.lift_ast_tac1 "<nm>")`. The
   `body_contract` binding at the end is the manual stand-in for the
   plugin's contract-assembly splice: it discharges 1-induction on
   `system_of_contract rely_core guar_core body_core`, derives
   `contract_valid` via `entailment_contract_all`, and produces the
   blessed `XContract` via `bless_contract`. *)
module Plugin.Test.Core.Contract

open Pipit.Source

module PPL  = Pipit.Plugin.Lift
module PSSB = Pipit.Prim.HasStream
module PPS  = Pipit.Prim.Shallow
module PXB  = Pipit.Exp.Base
module PXCB = Pipit.Exp.Checked.Base
module SI   = Pipit.System.Ind
module SX   = Pipit.System.Exp
module PT   = Pipit.Tactics

#set-options "--print_implicits --print_bound_var_types --print_full_names"


(* ----- 1. Source definitions ----- *)

[@@source_mode (ModeFun Stream true Stream)]
let rely (x: int): bool = x >= 0
%splice[] (PPL.lift_ast_tac1 "rely")

(* Result variable `r` comes LAST: the source-side convention puts
   the last param at de-Bruijn 0, which is where XContract.guar
   expects the body's result. *)
[@@source_mode (ModeFun Stream true (ModeFun Stream true Stream))]
let guar (x: int) (r: int): bool = r > 0
%splice[] (PPL.lift_ast_tac1 "guar")

(* `[@@proof_contract (`%rely) (`%guar)]` asks the plugin to splice a
   `body_contract` wrapper after `body_core`. The wrapper bundles
   `rely_core`, `guar_core`, `body_core` with
   `Pipit.Exp.Checked.Base.bless_contract` and discharges
   `induct1 (system_of_contract ...)` by normalisation. Source-level
   callers of `body` are then routed through the blessed contract via
   `find_core_for_source` (latest `core_of_source` wins).

   Because the synthesised wrapper references `rely_core` /
   `guar_core` by name, the rely and guar source bindings must be in
   scope before `body`'s declaration -- hence the reverse-order
   layout in this file. *)
[@@source_mode (ModeFun Stream true Stream); proof_contract (`%rely) (`%guar)]
let body (x: int): int = x + 1
%splice[] (PPL.lift_ast_tac1 "body")


(* ----- 2. Caller verification -----

  A source-level caller of `body` lifts to a cexp that references
  `body` by name. `Pipit.Source.Ast.Util.find_core_for_source` picks
  the most recently defined `[@@core_of_source body ...]` binding,
  which is `body_contract` (synthesised by `proof_contract`) -- not
  the raw `body_core` splice -- so the lifted core IR for the caller
  goes through the *blessed* contract. The caller's
  `[@@proof_induct1]` obligation thus reduces to "rely holds at the
  actual arg" rather than re-deriving the body's `(x + 1)` from
  scratch. *)

[@@source_mode (ModeFun Stream true Stream); proof_induct1]
let good_caller (_x: int): int = body 1
%splice[] (PPL.lift_ast_tac1 "good_caller")

(* Negative control: passing `-1` violates `body`'s `x >= 0` rely,
   so `[@@proof_induct1]` cannot discharge. `proof_expect_failure`
   makes the module typecheck iff that's what actually happens. *)
[@@source_mode (ModeFun Stream true Stream); proof_induct1; proof_expect_failure]
let bad_caller (_x: int): int = body (-1)
%splice[] (PPL.lift_ast_tac1 "bad_caller")
