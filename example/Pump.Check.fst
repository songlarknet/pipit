(* Checking our "pump" example *)
module Pump.Check

open Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics
module Sugar = Pipit.Sugar.Vanilla
module Check = Pipit.Sugar.Check

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
let min (a b: Sugar.ints) =
 let open Sugar in
 (if_then_else (a <=^ b) a b)

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
let countsecutive' (p: Sugar.bools) =
 let open Sugar in
 rec' (fun count ->
   if_then_else p
   (fby 1 (min (count +^ z1) (z count_max)))
   z0)

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
let lastn (n: int) (p: Sugar.bools) =
 let open Sugar in
 let' (countsecutive p) (fun c -> c >=^ z n)

let settle_time: int = 1000
let stuck_time:  int = 6000

(*
  node pump(
    estop_ok:  bool;
    level_low: bool;
  ) returns (
    pump_en:   bool;
    nok_stuck: bool;
  )
  let
    pump_en   =
        if nok_stuck
        then false
        else lastn(SETTLE, estop_ok and level_low);

    nok_stuck =
        any(lastn(STUCK, pump_en));

    --%PROPERTY "pump can never be engaged too long":
    --           not lastn(STUCK + 1, pump_en);
    --%PROPERTY "estop means not pumping":
    --          not estop_ok => not pump_en;
    --%PROPERTY "level high means not pumping":
    --          not level_low => not pump_en;
  tel

 We will rewrite this slightly to make it easier to state and prove. First, we
 will inline the two occurrences of lastn(_, pump_en) to share a binding for
 countsecutive(pump_en) so it's obvious they refer to the same count.

  node pump(
    estop_ok:  bool;
    level_low: bool;
  ) returns (
    pump_en:   bool;
    nok_stuck: bool;
  )
  var
    pump_try:  bool;
    count_en:  int;
  let
    pump_try  = lastn(SETTLE, estop_ok and level_low);

    count_en  = countsecutive(pump_try);

    nok_stuck =
        any(count_en >= STUCK);

    pump_en   = pump_try and not nok_stuck;

    --%PROPERTY "pump can never be engaged too long":
    --           count_en <= STUCK + 1;
    --%PROPERTY "estop means not pumping":
    --          not estop_ok => not pump_en;
    --%PROPERTY "level high means not pumping":
    --          not level_low => not pump_en;
  tel
*)

let controller_body (estop level_low: Sugar.bools) =
  let open Sugar in
  let' (countsecutive' (not_ estop /\ level_low)) (fun sol_try_c   ->
  let' (sol_try_c >=^ z settle_time)              (fun sol_try     ->
  let' (countsecutive' sol_try)                   (fun nok_stuck_c ->
  let' (once (nok_stuck_c >=^ z stuck_time))      (fun nok_stuck   ->
  let' (sol_try /\ not_ nok_stuck)                (fun sol_en      ->
  let' (tup sol_en nok_stuck)                     (fun result      ->
  check' "ESTOP OK"      (estop => not_ sol_en) (
  check' "LEVEL HIGH OK" (not_ level_low => not_ sol_en) (
    result))))))))

let controller =
  let e = Check.exp_of_stream2 controller_body in
  assert (Check.system_induct_k1 e) by (T.norm_full ());
  Check.stream_of_checked2 e
