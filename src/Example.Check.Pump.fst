(* Checking our "pump" example *)
module Example.Check.Pump

open Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = FStar.Tactics
module Sugar = Pipit.SugarX4

let tac_nbe (): T.Tac unit = T.norm [primops; iota; delta; zeta; nbe]

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
let min (a b: Sugar.s int) =
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
let countsecutive' (p: Sugar.s bool) =
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
let lastn (n: int) (p: Sugar.s bool) =
 let open Sugar in
 let' (countsecutive p) (fun c -> c >=^ z n)

let settle_time: int = 1000
let stuck_time:  int = 6000

let pair a b =
  let open Sugar in
  (fun a b -> (a, b)) <$> a <*> b

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
 countsecutive(pump_en) so it's obvious they refer to the same count. Second,
 Pipit only allows a single integer result (yet), so we'll add a result that
 encodes both results as a bitfield. The updated version is:

  node pump(
    estop_ok:  bool;
    level_low: bool;
  ) returns (
    return:    int;
  )
  var
    pump_try:  bool;
    pump_en:   bool;
    count_en:  int;
    nok_stuck: bool;
  let
    pump_try  = lastn(SETTLE, estop_ok and level_low);

    count_en  = countsecutive(pump_try);

    nok_stuck =
        ancount_en >= STUCK);

    pump_en   = pump_try and not nok_stuck;

    result    =
        (if pump_en then PUMP else 0) +
        (if nok_stuck then STUCK else 0);

    --%PROPERTY "pump can never be engaged too long":
    --           count_en <= STUCK + 1;
    --%PROPERTY "estop means not pumping":
    --          not estop_ok => not pump_en;
    --%PROPERTY "level high means not pumping":
    --          not level_low => not pump_en;
  tel
*)
// let controller (estop level_low: Sugar.s bool) =
//   let open Sugar in
//   // XXX: nesting is not working properly, for some reason inlining lastn helps
//   let' (lastn settle_time (not_ estop /\ level_low)) (fun sol_try ->
//   let' (once (lastn stuck_time sol_try)) (fun nok_stuck ->
//   let' (sol_try /\ not_ nok_stuck) (fun sol_en ->
//   let' (pair sol_en nok_stuck) (fun result ->
//   check' "ESTOP OK" (estop => not_ sol_try) (
//   check' "LEVEL HIGH OK"   (not_ level_low => not_ sol_try) (
//     result))))))

let controller' (estop level_low: Sugar.s bool) =
  let open Sugar in
  let' (countsecutive' (not_ estop /\ level_low)) (fun sol_try_c   ->
  let' (sol_try_c >=^ z settle_time)             (fun sol_try     ->
  let' (countsecutive' sol_try)                  (fun nok_stuck_c ->
  let' (once (nok_stuck_c >=^ z stuck_time))     (fun nok_stuck   ->
  let' (sol_try /\ not_ nok_stuck)                (fun sol_en      ->
  let' (pair sol_en nok_stuck)                   (fun result      ->
  check' "ESTOP OK"      (estop => not_ sol_try) (
  check' "LEVEL HIGH OK" (not_ level_low => not_ sol_try) (
    result))))))))

let controller_prop =
  system_of_exp (Sugar.run2 controller')

let controller_prop_prove (fv: sem_freevars): Lemma (ensures induct1 (controller_prop fv)) =
  assert (base_case (controller_prop fv)) by (tac_nbe (); T.dump "base");
  assert (step_case (controller_prop fv)) by (tac_nbe (); T.dump "step");
  ()
