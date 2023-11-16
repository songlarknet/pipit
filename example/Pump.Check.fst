(* Checking our "pump" example *)
module Pump.Check

open Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics
module Sugar = Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

open Pipit.Sugar.Vanilla

(*
   node min(
     a: int;
     b: int;
   ) returns (
     m: int;
   )
   let
     m = if a <= b then a else b;
   tel
*)
let min (#ty: Sugar.arithtype) (a b: Sugar.s ty) =
 if_then_else (a <=^ b) a b

(* We need to limit integers so they don't overflow.
   This isn't yet checked by the proofs. *)
let count_max = 65535

(*
   node countsecutive(
     p:     bool;
   ) returns (
     count: int;
   )
   let
     count =
        if   p
        then min((0 -> pre count) + 1, count_max)
        else 0;
   tel
*)
let countsecutive_body (p: Sugar.bools) =
  rec' (fun count ->
    if_then_else
      p
      (fby 1 (min (count +^ z1) (z count_max)))
      z0)
  `check_that` (fun count -> z0 <=^ count)

let countsecutive': Sugar.bools -> Sugar.ints =
  let e = Check.exp_of_stream1 countsecutive_body in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Pump"]);
  Check.stream_of_checked1 e

(*
   node lastn(
     const n: int
           p: bool;
   ) returns (
     ok:      bool;
   )
   let
     ok = countsecutive(p) >= n;
   tel
*)
let lastn (n: nat) (p: Sugar.bools) =
 countsecutive' p >=^ z n

let anyn (n: nat) (p: Sugar.bools) =
 countsecutive' (not_ p) <^ z n

// let check_lastn_anyn_dual (n: nat): unit =
//   // TODO:CSE: needs CSE and extra invariant: countsecutive' p =^ countsecutive' (not (not p))
//   // or with manual rewrites:
//   // > (countsecutive p >= n) = not (counsecutive (not (not p)) < n)
//   // rewrite not.not
//   // > (countsecutive p >= n) = not (counsecutive p < n)
//   // rewrite not.<
//   // > (countsecutive p >= n) = (counsecutive p >= n)
//   // rewrite refl
//   // > true
//   let e = Check.exp_of_stream1 (fun p ->
//     check ""
//       (lastn n p =^ not_ (anyn n (not_ p)))) in
//   assert (Check.system_induct_k1 e) by (T.norm_full ())

let settle_time: int = 1000
let stuck_time:  int = 6000

(*
  node pump(
    estop_ok:  bool;
    level_low: bool;
  ) returns (
    sol_en:   bool;
    nok_stuck: bool;
  )
  var sol_try: bool;
  let
    sol_try   = lastn(SETTLE, estop_ok and level_low);
    nok_stuck = any(lastn(STUCK, pump_en));
    sol_en    = sol_try and not nok_stuck;

    --%PROPERTY "estop means not pumping":
    --          not estop_ok => not pump_en;
    --%PROPERTY "level high means not pumping":
    --          not level_low => not pump_en;
  tel
*)

(* TODO:CSE: once we have CSE, we can use regular lets and the syntax will be a little nicer: *)
// let controller_body_lets (estop level_low: Sugar.bools) =
//   let sol_try   = lastn settle_time (not_ estop /\ level_low) in
//   let nok_stuck = once (lastn stuck_time sol_try) in
//   let sol_en    = sol_try /\ not_ nok_stuck in
//     tup sol_en nok_stuck
//       `check_that` (fun _ ->      estop     => not_ sol_en)
//       `check_that` (fun _ -> not_ level_low => not_ sol_en)

let controller_body (estop level_low: Sugar.bools) =
  let' (lastn settle_time (not_ estop /\ level_low)) (fun sol_try   ->
  let' (once (lastn stuck_time sol_try))             (fun nok_stuck   ->
  let' (sol_try /\ not_ nok_stuck)                   (fun sol_en      ->
    tup sol_en nok_stuck
      // PROPERTY estop means not pumping
      `check_that` (fun _ ->      estop     => not_ sol_en)
      // PROPERTY level high means not pumping
      `check_that` (fun _ -> not_ level_low => not_ sol_en))))

let controller =
  let e = Check.exp_of_stream2 controller_body in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Pump"]);
  Check.stream_of_checked2 e

let reservoir_model (flow: Sugar.ints) (sol_en: Sugar.bools) =
  rec' (fun level ->
    (0 `fby` level) +^ (if_then_else sol_en flow (min flow z0)))

let max_flow  = 10
let level_low_threshold = 80
let max_level = 100

let spec_body (flow: Sugar.ints) (estop level_low: Sugar.bools) =
  let' (controller_body estop level_low) (fun ctrl ->
  let' (fst ctrl)                        (fun sol_en ->
  let' (reservoir_model flow sol_en)     (fun level ->
  check "SPEC"
    (sofar (abs flow <^ z max_flow) =>
     (sofar (level >^ z level_low_threshold => not_ level_low) =>
     (level <^ z max_level))))))

let spec =
  let e = Check.exp_of_stream3 spec_body in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Pump"]);
  Check.stream_of_checked3 e

let spec_any_needs_extra_invariant_manual_cse (flow: Sugar.ints) (estop level_low: Sugar.bools) =
  let' (countsecutive' (not_ estop /\ level_low))    (fun sol_try_c   ->
  let' (countsecutive' level_low)                    (fun level_low_c   ->
  let' (sol_try_c >=^ z settle_time)                 (fun sol_try   ->
  let' (once (lastn stuck_time sol_try))             (fun nok_stuck   ->
  let' (sol_try /\ not_ nok_stuck)                   (fun sol_en      ->
  let' (reservoir_model flow sol_en)                 (fun level ->
  check' "INVARIANT: countsecutive(x /\ y) <= countsecutive(y)"
    (sol_try_c <=^ level_low_c) (
  check "SPEC"
    (sofar (abs flow <^ z max_flow) =>
    (sofar (level >^ z level_low_threshold => (level_low_c <^ z settle_time)) =>
    (level <^ z max_level))))))))))

let spec_any' =
  let e = Check.exp_of_stream3 spec_any_needs_extra_invariant_manual_cse in
  assert (Check.system_induct_k1 e) by (T.norm_full ["Pump"]);
  Check.stream_of_checked3 e
