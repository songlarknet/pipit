(* Regression test for the former README workaround §10:
   `cfg.field.fun_subfield <stream> ...` where the projected subfield
   has function type. The TTCan2 blocker was

     let trigger_enabled (cfg: config) (ix: stream index) (c: cycle): stream bool =
       cfg.triggers.enabled ix c

   which used to fail the lifter with "Variable cfg not found".

   FIXED 2026-06-08 in `Pipit.Source.Ast.Lower`. Background:

   `Pipit.Source.Ast.Reflect.lift_app_fv`'s pre-static-prefix path
   recognises that `(Mkconfig?.triggers cfg)` is splice-safe (because
   `cfg` is a top-level Static binder with `ob_top_level = true`) and
   pre-applies it to `Mktrigger_array?.enabled`, producing
   `prim_fn = cfg.triggers.enabled : index -> cycle -> bool`.

   `Pipit.Source.Ast.Lower.shallow_prim` (via `flush_prim_acc`) then
   hoists this prim to a top-level `__xprim_<src>_<N>` helper sigelt.
   The hoist USED to wrap the helper in `Tv_Abs` over
   `env.ctx_passthrough` only (the polymorphic type / instance
   binders), so the emitted helper had a free `cfg`:

     let __xprim_trigger_read_at_6 : prim =
       Mkprim None _ cfg.triggers.enabled

   The fix adds `static_binders` to `lower_env` (parallel to
   `ctx_passthrough`) and makes both `intern_prim` (call site) and
   `flush_prim_acc` (definition site) close over both. Hoisted helpers
   now look like

     let __xprim_trigger_read_at_6 (cfg: config) : prim =
       Mkprim None _ cfg.triggers.enabled

   and call sites pass `cfg` explicitly. Scalar projections like
   `cfg.triggers.size` continue to use `xval` (no prim hoist) and
   stay inline. *)
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
   BASELINE — scalar subfield projection (unaffected by the bug,
   regression-test that the fix didn't break this path).
   `cfg.triggers.size` lowers to `xval` (no prim hoist) so the
   inline reference stays scoped by the outer `Tv_Abs cfg` of
   the spliced sigelt.
   ============================================================ *)
let size_const (cfg: config): stream int =
  cfg.triggers.size

(* ============================================================
   PROBE 1 — direct inline call. Used to fail with
     "Error 230 ... Variable \"cfg\" not found"
   Now works: the hoisted `__xprim_probe1_inline_N` helper
   takes `cfg` as an explicit parameter.
   ============================================================ *)
let probe1_inline (cfg: config) (ix: stream index) (c: cycle): stream bool =
  cfg.triggers.enabled ix c

(* ============================================================
   PROBE 2 — plain (no [@@source_mode]) wrapper. Used to fail
   identically; now works for the same reason.
   ============================================================ *)
let enabled_at (cfg: config) (ix: index) (c: cycle): bool =
  cfg.triggers.enabled ix c

let probe2_wrapper (cfg: config) (ix: stream index) (c: cycle): stream bool =
  enabled_at cfg ix c

(* ============================================================
   PROBE 3 — manually [@@source_mode]-annotated wrapper with an
   all-Static signature (no `stream` in the user-facing types).
   Used to fail with the same Error 230; now works.
   ============================================================ *)
[@@source_mode (ModeFun Static true (ModeFun Stream true (ModeFun Static true Stream)))]
let trigger_read_at (cfg: config) (ix: index) (c: cycle): bool =
  cfg.triggers.enabled ix c
%splice[] (PPL.lift_ast_tac1 "trigger_read_at")

let probe3_caller (cfg: config) (ix: stream index) (c: cycle): stream bool =
  trigger_read_at cfg ix c
