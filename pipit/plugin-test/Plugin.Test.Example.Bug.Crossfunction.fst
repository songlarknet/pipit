module Plugin.Test.Example.Bug.Crossfunction
#lang-pipit

(*
  Regression test for a cross-function lift mismatch.

  Previously: when a stream function [callee] took two or more stream
  arguments of *different* types, calling [callee] from another stream
  function failed with F* error 19 (subtyping check failed). The
  symptom looked like a type-alias opacity issue
  ([get_index [a; b] 1] vs the callee's alias) but the real cause was
  an argument-to-type ordering bug in [lift_tm_lifted_apps_strm].

  Root cause: [strm_apps] is reversed to source order (oldest binding
  first) before being passed to [lift_tm_lifted_apps_strm], but [tys]
  from [get_exp_context hd] is in callee's DB order (newest binding
  first). The two lists were zipped without re-aligning, so each
  [XLet] in the chain was built with the wrong binding type. With
  same-type callees the misalignment was invisible because every
  position held the same type; with mixed types the type at each
  [XLet] position got swapped and F* reported an unprovable subtype
  obligation that referenced [get_index ... 1] on the wrong list.

  Fix: reverse [tys] at the call site so it aligns with [strm_apps].
  [tys_all] (used by the base-case [weaken]) stays in DB order.
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

(* 3-arg mixed-type callee: (int, bool, int) -> int. The middle bool
  argument is placed between two ints so that any single-position swap
  in the lift's argument/type alignment would surface as a type error. *)
let add_mixed3 (a: stream int) (b: stream bool) (c: stream int): stream int =
  (if b then a else c) + c

(* -- callers: cases that WORK ----------------------------------------- *)

(* 1-arg cross-call: OK. *)
let caller_inc (x: stream int): stream int =
  inc_int x

(* 2-arg same-type cross-call: OK. *)
let caller_same (x: stream int): stream int =
  add_same x (x + 1)

(* 2-arg mixed-type cross-call: regression test for the ordering bug. *)
let caller_mixed (x: stream int) (b: stream bool): stream int =
  add_mixed x b

(* 3-arg mixed-type cross-call, args passed in source order. *)
let caller_mixed3 (x: stream int) (b: stream bool) (y: stream int): stream int =
  add_mixed3 x b y

(* 3-arg mixed-type cross-call where the caller's args appear in a
  different order than the callee expects. This exercises the lift's
  per-position type alignment more thoroughly. *)
let caller_mixed3_reordered (b: stream bool) (y: stream int) (x: stream int): stream int =
  add_mixed3 x b y
