(* Simple Pulse-based integration for mutable state extraction. *)
module Pipit.Exec.Pulse
#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

module EE = Pipit.Exec.Exp
module Tac = FStar.Tactics

let tac_extract_full_strong_core (namespaces: list string) (local_delta: list string) =
  let base_delta = [
    "Pipit.Exec.Pulse.mk_step_pure";
    "Pipit.Context.Row.index";
    "FStar.Pervasives.coerce_eq"
  ] in
  Tac.norm [
    nbe;
    primops;
    iota;
    zeta;
    delta_namespace ("Pipit" :: "FStar.Pervasives" :: namespaces);
    delta_only (local_delta @ base_delta);
    delta_qualifier ["inline_for_extraction"];
    delta_attr [`%Pipit.Tactics.norm_attr]
  ];
  Tac.norm [
    zeta_full;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only local_delta
  ]

let tac_normalize_pure (namespaces: list string) () =
  Pipit.Tactics.norm_full namespaces;
  Tac.trefl ()

(*
let tac_extract (namespaces: list string) () =
  let opts ns = [
    nbe;
    primops;
    iota;
    zeta_full;
    delta_namespace ("Pipit" :: "FStar.Pervasives" :: ns);
    delta_qualifier ["inline_for_extraction"];
    delta_attr [`%Pipit.Tactics.norm_attr]
  ] in
  Tac.norm (opts namespaces);
  Tac.trefl ()
*)

noextract inline_for_extraction
let mk_init (#input #state #output: Type)
  (t: EE.esystem input state output)
  : state
=
  match t with
  | { init = init_v; step = _ } -> init_v

noextract inline_for_extraction
let mk_step_pure (#input #state #output: Type)
  (t: EE.esystem input state output)
  (inp: input)
  (st: state)
  : (state & output)
=
  match t with
  | { init = _; step = step_f } -> step_f inp st

noextract inline_for_extraction
fn mk_reset (#state: eqtype)
  (init_v: state)
  (st: ref state)
  requires R.pts_to st 'n
  ensures R.pts_to st init_v
{
  st := init_v
}

noextract inline_for_extraction
fn mk_step (#input #result #state: eqtype)
  (step_f: input -> state -> (state & result))
  (inp: input)
  (st: ref state)
  requires R.pts_to st 'n
  returns out: result
  ensures R.pts_to st (fst (step_f inp 'n))
  ensures pure (out == snd (step_f inp 'n))
{
  let s = !st;
  let next = step_f inp s;
  let s' = fst next;
  let out = snd next;
  st := s';
  out
}

noextract inline_for_extraction
fn mk_reset_sys (#input #state #output: eqtype)
  (t: EE.esystem input state output)
  (st: ref state)
  requires R.pts_to st 'n
  ensures R.pts_to st (mk_init t)
{
  st := mk_init t
}

noextract inline_for_extraction
fn mk_step_sys (#input #state #output: eqtype)
  (t: EE.esystem input state output)
  (inp: input)
  (st: ref state)
  requires R.pts_to st 'n
  returns out: output
  ensures R.pts_to st (fst (mk_step_pure t inp 'n))
  ensures pure (out == snd (mk_step_pure t inp 'n))
{
  let s = !st;
  let next = mk_step_pure t inp s;
  let s' = fst next;
  let out = snd next;
  st := s';
  out
}

(* Strong-enough normalization for extracting both single- and multi-input
  Pulse systems. The deltas are written for the common case where the
  result of [mk_step]/[mk_reset] is normalized down to plain Pulse with
  no surviving [Pipit_Context_Row_index] / [coerce_eq__any_any] calls.

  Two subtle requirements (both load-bearing for the multi-input case):

  * [zeta_full] instead of plain [zeta]. The recursive case of
    [Pipit.Context.Row.index] introduces a let-binding [ts = ...] via an
    [iota]-match on the row list; plain [zeta] does not propagate that
    binding deeply enough for the recursive [index] call to fire, so
    the recursion stalls. With [zeta_full] the substitution happens and
    the recursion fully unfolds.

  * [FStar.Pervasives.coerce_eq] in [delta_only]. The recursive case of
    [Row.index] wraps its result in [coerce_eq] to reconcile two
    index-list views; without unfolding the coercion the wrapper
    survives in C as an unimplemented [coerce_eq__any_any] call. *)
let tac_extract (namespaces: list string) () =
  Tac.norm [
    zeta_full;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only [
      `%mk_init;
      `%mk_step_pure;
      `%mk_reset;
      `%mk_step;
      `%mk_reset_sys;
      `%mk_step_sys;
      `%Pipit.Context.Row.index;
      `%FStar.Pervasives.coerce_eq;
    ]
  ];
  Tac.trefl ()

let tac_extract_full_generic (namespaces: list string) (local_delta: list string) () =
  let base_delta = [
    "Pipit.Exec.Pulse.mk_step_pure";
    "Pipit.Context.Row.index";
    "FStar.Pervasives.coerce_eq"
  ] in
  let opts ns = [
    nbe;
    primops;
    iota;
    zeta;
    delta_namespace ("Pipit" :: "FStar.Pervasives" :: ns);
    delta_only (local_delta @ base_delta);
    delta_qualifier ["inline_for_extraction"];
    delta_attr [`%Pipit.Tactics.norm_attr]
  ] in
  Tac.norm (opts namespaces);
  Tac.trefl ()

let tac_specialize_generic (namespaces: list string) (local_delta: list string) () =
  Tac.norm [
    zeta;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only (local_delta @ [
      "Pipit.Exec.Pulse.mk_init";
      "Pipit.Exec.Pulse.mk_step_pure";
      "Pipit.Exec.Pulse.mk_reset";
      "Pipit.Exec.Pulse.mk_step";
      "Pipit.Exec.Pulse.mk_reset_sys";
      "Pipit.Exec.Pulse.mk_step_sys";
      "Pipit.Context.Row.index";
      "FStar.Pervasives.coerce_eq"
    ])
  ];
  Tac.trefl ()

let tac_extract_full_strong_generic (namespaces: list string) (local_delta: list string) () =
  tac_extract_full_strong_core namespaces local_delta;
  Tac.trefl ()

let tac_specialize_strong_generic (namespaces: list string) (local_delta: list string) () =
  let base_delta = [
    "Pipit.Exec.Pulse.mk_init";
    "Pipit.Exec.Pulse.mk_step_pure";
    "Pipit.Exec.Pulse.mk_reset";
    "Pipit.Exec.Pulse.mk_step";
    "Pipit.Exec.Pulse.mk_reset_sys";
    "Pipit.Exec.Pulse.mk_step_sys";
    "Pipit.Context.Row.index";
    "FStar.Pervasives.coerce_eq"
  ] in
  Tac.norm [
    zeta;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only (local_delta @ base_delta)
  ];
  Tac.norm [
    zeta_full;
    iota;
    primops;
    delta_namespace namespaces;
    delta_only local_delta
  ];
  Tac.trefl ()

