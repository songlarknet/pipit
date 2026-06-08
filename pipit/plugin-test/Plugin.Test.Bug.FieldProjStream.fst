(* Standalone reproducer for README workaround §10:
   `cfg.field.fun_subfield <stream> ...` where the projected subfield
   has function type. The TTCan2 blocker is

     let trigger_enabled (cfg: config) (ix: stream index) (c: cycle): stream bool =
       cfg.triggers.enabled ix c

   which fails the lifter with "Variable cfg not found".

   ROOT CAUSE (verified 2026-06-08 via `--ext pipit:lift:debug`).
   `Pipit.Source.Ast.Reflect.lift_app_fv`'s pre-static-prefix path
   correctly recognises that `(Mkconfig?.triggers cfg)` is
   splice-safe (because `cfg` is a top-level Static binder with
   `ob_top_level = true`) and pre-applies it to
   `Mktrigger_array?.enabled`. The resulting `prim_fn` is
   `cfg.triggers.enabled : index -> cycle -> bool`. So far so good.

   But `Pipit.Source.Ast.Lower.shallow_prim` then hoists every prim
   to a top-level `__xprim_<src>_<N>` helper sigelt (via
   `flush_prim_acc`). The hoist wraps the helper definition in
   `Tv_Abs` over `env.ctx_passthrough` (the polymorphic type /
   typeclass-instance binders) — but NOT over the explicit Static
   binders that the prim_fn references. The emitted top-level
   sigelt

     let __xprim_trigger_read_at_6 : prim =
       Mkprim None _ cfg.triggers.enabled

   has a FREE `cfg`, which F* immediately rejects with
   `Error 230: Variable "cfg" not found` pointing at the original
   source location of the `cfg.triggers.enabled` call.

   This is a lifter bug, not a missing feature: a fix needs to
   either avoid hoisting prims that reference local Static binders,
   or wrap each helper in extra `Tv_Abs` over the referenced
   Statics and update the call site (`shallow_prim`'s return) to
   apply them. None of the user-side workarounds tried in this file
   (plain wrapper, manual `[@@source_mode]` wrapper, plain F*
   helper exposing the function field) close the gap because all of
   them ultimately route the `cfg.triggers.enabled` term through
   `shallow_prim`.

   Compare: `cfg.triggers.size` (SCALAR field) in `size_const`
   below works fine — `xval` keeps `cfg.triggers.size` inline in
   the spliced body (still scoped by the outer `Tv_Abs cfg`),
   without going through the prim-hoist path. *)
module Plugin.Test.Bug.FieldProjStream
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Plugin.Interface  // for ModeFun / Static / Stream
module PPL  = Pipit.Plugin.Lift
module PSSBH = Pipit.Prim.HasStream

#set-options "--warn_error -242"

type index = int
type cycle = int

(* Function-typed record field — the shape that bites in
   Network.TTCan.TriggerTimely.trigger_array. *)
noeq
type trigger_array = {
  size:      int;
  enabled:   index -> cycle -> bool;
  time_mark: index -> int;
}

(* Outer record holding a trigger_array. Mirrors TTCan's [config]. *)
noeq
type config = {
  triggers: trigger_array;
}

(* ============================================================
   BASELINE — pure projection of a SCALAR subfield works.
   Mirrors the working `cfg.triggers.ttcan_exec_period` pattern
   in `Network.TTCan.Impl.Util.cycle_time_valid`. The projection
   lowers to `xval` (no prim hoist) so the inline
   `cfg.triggers.size` reference stays scoped by the outer
   `Tv_Abs cfg` of the spliced sigelt.
   ============================================================ *)
let size_const (cfg: config): stream int =
  cfg.triggers.size

(* ============================================================
   PROBE 1 — direct inline call. Reproduces the TTCan2 blocker:
     "Error 230 ... Variable \"cfg\" not found"
   Commented out so the rest of the file can compile.
   ============================================================ *)
(*
let probe1_inline (cfg: config) (ix: stream index) (c: cycle): stream bool =
  cfg.triggers.enabled ix c
*)

(* ============================================================
   PROBE 2 — plain (no [@@source_mode]) wrapper. Fails
   identically: the call site `enabled_at cfg ix c` sees `cfg`
   as a top-level Static binder (splice-safe), so the pre-static
   prefix path fires and produces `prim_fn = enabled_at cfg`,
   which is then hoisted by `shallow_prim` — same free-`cfg`
   bug.
   ============================================================ *)
(*
let enabled_at (cfg: config) (ix: index) (c: cycle): bool =
  cfg.triggers.enabled ix c

let probe2_wrapper (cfg: config) (ix: stream index) (c: cycle): stream bool =
  enabled_at cfg ix c
*)

(* ============================================================
   PROBE 3 — manually [@@source_mode]-annotated wrapper with an
   all-Static signature (no `stream` in the user-facing types).
   The mode attribute tells the lifter that `ix` is Stream-bound
   at lifted call sites; the wrapper body `cfg.triggers.enabled
   ix c` is plain F* (no stream args at the source level), so
   F* typechecks the user-facing wrapper normally.

   Inside the lifted body, `cfg` IS a top-level Static binder of
   the lifted sigelt, so `term_safe_at_splice` returns true and
   the pre-static-prefix path fires correctly. The resulting
   `prim_fn = cfg.triggers.enabled` is hoisted to a top-level
   `__xprim_trigger_read_at_<N>` helper where `cfg` is free —
   same Error 230.

   Verified via `--ext pipit:lift:debug` which prints
     hoisted prim helper:
       Plugin.Test.Bug.FieldProjStream.__xprim_trigger_read_at_6
         := Mkprim None _ cfg.triggers.enabled
   immediately before F* rejects the splice.

   Commented out so the rest of the file compiles; uncomment to
   reproduce.
   ============================================================ *)
(*
[@@source_mode (ModeFun Static true (ModeFun Stream true (ModeFun Static true Stream)))]
let trigger_read_at (cfg: config) (ix: index) (c: cycle): bool =
  cfg.triggers.enabled ix c
%splice[] (PPL.lift_ast_tac1 "trigger_read_at")

let probe3_caller (cfg: config) (ix: stream index) (c: cycle): stream bool =
  trigger_read_at cfg ix c
*)
