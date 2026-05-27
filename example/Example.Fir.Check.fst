module Example.Fir.Check
#lang-pipit

(* A small bounded-input/bounded-output proof for a Finite Impulse
   Response (FIR) filter.

   Port of the deleted example/Fir.Check.fst's [bibo2]. The original used
   the (now-removed) Pipit.Sugar.Vanilla + Pipit.Sugar.Check surface and
   hand-rolled the k-induction; here we let the [#lang-pipit] plugin do
   the lift and discharge the check with [@@proof_induct1]. *)

open Pipit.Source
module PSSB = Pipit.Sugar.Shallow.Base

(* Temporal: sofar p == p has held at every step so far. *)
let sofar (p: stream bool): stream bool =
  let rec r = p && (true `fby` r) in
  r

(* Two-tap FIR filter:  y[n] = 7 * x[n] + 3 * x[n-1].  The sum of the
   absolute values of the coefficients (|7| + |3| = 10) bounds the output
   for any bounded input. *)
let fir2 (input: stream int): stream int =
  input * 7 + (0 `fby` input) * 3

let bound: int = 100

(* BIBO: if every past input was within [-bound, bound], then the output
   is within [-10*bound, 10*bound]. This holds by 1-induction because the
   filter's state is one element deep. *)
[@@proof_induct1]
let bibo2 (signal: stream int): stream unit =
  check
    (sofar (abs signal <= bound) ==>^
    (abs (fir2 signal) <= bound * 10))

(* -------------------------------------------------------------------- *)
(* Things we'd like to bring back but can't yet:

   * bibo3 -- the same property for a three-tap filter
       y[n] = 7 * x[n] + 2 * x[n-1] + 1 * x[n-2]
     The filter's state is now two elements deep, so the BIBO invariant
     needs 2-induction. The plugin currently only synthesises 1-induction
     obligations (Pipit_Plugin_Attributes / Pipit_Plugin_Preprocess only
     handle proof_induct1). Generalising to [@@proof_induct k] would
     unlock bibo3 and also help the disabled example/ttcan/ port.

       let fir3 (input: stream int): stream int =
         let pre1 = 0 `fby` input in
         let pre2 = 0 `fby` pre1  in
         input * 7 + pre1 * 2 + pre2 * 1

       [@@proof_induct 2]  // <-- not implemented yet
       let bibo3 (signal: stream int): stream unit =
         check (sofar (abs signal <= bound) ==>^
                abs (fir3 signal) <= bound * 10)

   * FirN -- the original example/Fir.CheckN.fst built an N-tap FIR by
     F* list induction over the coefficient list, discharging a
     bounded-output contract at each recursive step. That mixes runtime
     list induction with Pipit stream proofs; the plugin lifts one
     function body at a time and has no story for synthesising one
     core expression per recursive F* call. A clean fix probably comes
     with the new IR frontend; until then the technique lives only in
     git history (see commit 9a61077^ : example/Fir.CheckN.fst).
*)
