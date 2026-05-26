module Plugin.Test.Example.Bug.Crossfunction
#lang-pipit

(*
  Standalone reproducer for the cross-function lift mismatch.

  Symptom: when a stream function [callee] takes two or more stream
  arguments of *different* types, calling [callee] from another stream
  function fails with F* error 19 (subtyping check failed). The
  expected type uses the callee's shallow type alias (e.g.
  [callee__prim_3 : Type0]) while the produced argument's type goes
  through the caller's alias list (e.g.
  [get_index [caller__prim_6; caller__prim_3] 1]). Both unfold to the
  same underlying type ([PSSB.shallow bool]) but F* does not unfold
  these nominal aliases during conversion, so subtyping fails.

  Exact error shape (see [caller_mixed_FAILS] below, commented out):

      * Error 19 at Plugin.Test.Example.Bug.Crossfunction.fst(...):
        - Subtyping check failed
        - Expected type
            Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
              [caller_mixed_FAILS__prim_6; caller_mixed_FAILS__prim_3]
              add_mixed__prim_6
          got type
            Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
              [caller_mixed_FAILS__prim_6; caller_mixed_FAILS__prim_3]
              (Pipit.Context.Base.get_index
                  [caller_mixed_FAILS__prim_6;
                   caller_mixed_FAILS__prim_3]
                  1)

  Root cause: in [Pipit.Plugin.Lift.fst], [env_get_shallow_ty] caches
  per-top-level shallow type aliases under names of the form
  [<func_prefix>__prim_<N>]. The cache is reset for each [env_top]
  invocation, so each top-level lift produces its own aliases. When
  the caller's lift constructs the [XLet] chain around a cross-function
  call ([lift_tm_lifted_apps_strm]) the expected type [t] comes from
  the callee's lifted context ([get_exp_context hd e]) while the
  argument [s] was lifted in the caller's env. The two aliases are
  nominally distinct and F* refuses to unfold them.

  Why single-arg / same-type-multi-arg cases work: when every argument
  has the same shallow type, the expected and got types in the [XLet]
  body collapse to the same alias-list-indexed expression (e.g.
  [get_index [...] 0]) which F* manages to convert; with mixed types
  the indices differ between the callee and caller and the conversion
  gives up.

  Possible fixes (not yet attempted):
    - Mark the synthesised shallow aliases as [unfold] when emitting
      them in [core_sigelt] so F* normalises them during subtyping.
    - Share [shallow_cache] across [env_top] invocations so every
      top-level shares the same alias names (more invasive).

  Working cases stay enabled. The failing case at the bottom is
  commented out to keep this module clean; uncomment it to reproduce.
*)

open Pipit.Source
module PSSB = Pipit.Sugar.Shallow.Base

instance has_stream_int: PSSB.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

(* -- callees ----------------------------------------------------------- *)

let inc_int (x: stream int): stream int =
  x + 1

(* All-same-type callee. *)
let add_same (a b: stream int): stream int =
  a + b

(* Mixed-type callee: (int, bool) -> int. *)
let add_mixed (a: stream int) (b: stream bool): stream int =
  a + (if b then 0 else 1)

(* -- callers: cases that WORK ----------------------------------------- *)

(* 1-arg cross-call: OK. *)
let caller_inc (x: stream int): stream int =
  inc_int x

(* 2-arg same-type cross-call: OK. *)
let caller_same (x: stream int): stream int =
  add_same x (x + 1)

(* -- callers: case that FAILS ----------------------------------------- *)

(*
  BUG: 2-arg mixed-type cross-call. Uncomment to observe Error 19.
  Both [_prim_N] aliases unfold to the same [PSSB.shallow] type but
  F* does not unfold them during conversion.
*)
// let caller_mixed_FAILS (x: stream int) (b: stream bool): stream int =
//   add_mixed x b
