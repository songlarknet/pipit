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

let pump_flag:   int = 1
let stuck_flag:  int = 2

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
let pump (estop_ok level_low: exp) (mk_prop: bool) =
  let open Sugar in
  let pump_try =
    lastn settle_time (estop_ok /\ level_low)
  in
  let count_en (pump_try': exp) =
    countsecutive' pump_try'
  in
  let nok_stuck (count_en': exp) =
    once (count_en' >=^ z stuck_time)
  in
  let pump_en (pump_try' nok_stuck': exp) =
    pump_try' /\ !nok_stuck'
  in
  let result (pump_en' nok_stuck': exp) =
    (ite pump_en'   (z  pump_flag) z0) +^
    (ite nok_stuck' (z stuck_flag) z0)
  in
  let prop (estop_ok' level_low' count_en' pump_en': exp) =
    // (count_en' >=^ z stuck_time) /\
    (!estop_ok' => !pump_en') /\
    (!level_low' => !pump_en')
  in
  let' pump_try (
    let' (count_en x0) (
      let' (nok_stuck x0) (
        let' (pump_en x2 x0) (
          if mk_prop
          then prop (lift_by estop_ok 0 4) (lift_by level_low 0 4) x2 x0
          else result x0 x1))))

let pump_prop_x = pump (XVar 1) (XVar 0) true
let pump_prop_n = 2

let pump_prop =
  assert_norm (wf pump_prop_x pump_prop_n);
  system_of_exp pump_prop_x pump_prop_n

let pump_prop_prove (): Lemma (ensures induct1' pump_prop) =
  assert (base_case' pump_prop) by tac_nbe ();
  assert (step_case' pump_prop) by tac_nbe ();
  ()
