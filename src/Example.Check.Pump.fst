(* Checking our "pump" example *)
module Example.Check.Pump

open Pipit.Exp.Base
open Pipit.Exp.Subst

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = FStar.Tactics
module Sugar = Pipit.Sugar

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
let min (a b: exp) =
 let open Sugar in
 (ite (a <=^ b) a b)
 // XXX: introducing let-binding here breaks proof - why?
 // let' a (let' (lift' b) (
 //    ite (x1 <=^ x0) x1 x0))

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
let countsecutive' (p: exp) =
 let open Sugar in
 mu' (
    let count = XVar 0 in
    let p' = lift' p in
    // simplified to make C code a little bit simpler, as pre is 0-initialised
    ite p' (pre (min (count +^ z1) (z count_max))) z0)

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
let lastn (n: int) (p: exp) =
 let open Sugar in
 countsecutive' p >=^ z n

let settle_time: int = 100
let stuck_time:  int = 6000

let solenoid_flag: int = 1
let stuck_flag:    int = 2

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
let controller (estop level_low: exp) (mk_prop: bool) =
  let open Sugar in
  let sol_try =
    lastn settle_time (!estop /\ level_low)
  in
  let nok_stuck (sol_try': exp) =
    once (lastn stuck_time sol_try')
  in
  let sol_en (sol_try' nok_stuck': exp) =
    sol_try' /\ !nok_stuck'
  in
  let result (sol_en' nok_stuck': exp) =
    (ite sol_en'    (z solenoid_flag) z0) +^
    (ite nok_stuck' (z stuck_flag) z0)
  in
  let prop (estop' level_low' sol_en': exp) =
    (estop' => !sol_en') /\
    (!level_low' => !sol_en')
  in
  let' sol_try (
    let' (nok_stuck x0) (
      let' (sol_en x1 x0) (
        if mk_prop
        then prop (lift_by estop 0 3) (lift_by level_low 0 3) x0
        else result x0 x1)))

let controller_prop_x = controller (XVar 1) (XVar 0) true
let controller_prop_n = 2

let controller_prop =
  assert_norm (wf controller_prop_x controller_prop_n);
  system_of_exp controller_prop_x controller_prop_n

let controller_prop_prove (): Lemma (ensures induct1' controller_prop) =
  assert (base_case' controller_prop) by tac_nbe ();
  assert (step_case' controller_prop) by tac_nbe ();
  ()
