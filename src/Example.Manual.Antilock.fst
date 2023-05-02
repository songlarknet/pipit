module Example.Manual.Antilock

open FStar.Mul
open FStar.Ref

(* Distance in millimetres, because the wheel is 235mm *)
type distance = int

(* Represent speed as millimetres per second so we don't need floats.
   1km/h ~ 277mm/s
   50km/h ~ 13888mm/s
*)
type speed = int

(* millimetres per second per second *)
type accel = int

(* angular velocity in 1000ths of a revolution per second *)
type angular_velocity = int

let within_tolerance (b1 b2: int) (tolerance: int): bool =
  let diff = b1 - b2 in
  -tolerance <= diff && diff <= tolerance

let wheel_circ: distance = 235 * 2

let gravity: accel = 9800

(* accelerometer tolerance is ±80mg (milligravities?) *)
let accelerometer_tolerance: speed = gravity * 80 / 1000

let max x y = if x >= y then x else y

(* allow for 5% difference in wheel circumferences.
  this is about 23mm (almost an inch), at 40 rps ~ 35km/h is 1km/h tolerance. *)
let wheel_tolerance: angular_velocity = 1000 * 5 / 100 * 40
let wheel_tolerance_speed: speed = (wheel_tolerance * wheel_circ) / 1000

(* Imperative implementation *)

type inputs = {
  wheel_front:  angular_velocity;
  wheel_rear:   angular_velocity;
  accel_z:      accel;
}
type estimate = {
  speed_lo: speed; speed_hi: speed;
}

let estimate_init: estimate = {
  speed_lo = 0; speed_hi = 0;
}

let estimate_update (i: inputs) (pre: estimate): estimate =
  let front: speed = (i.wheel_front * wheel_circ) / 1000 in
  let rear:  speed = (i.wheel_rear  * wheel_circ) / 1000 in
  let min_vel: speed = min front rear                    in
  let max_vel: speed = max front rear                    in

  let ok = within_tolerance i.wheel_front i.wheel_rear wheel_tolerance in

  let lo = if ok then min_vel else pre.speed_lo + i.accel_z - accelerometer_tolerance in
  let hi = if ok then max_vel else pre.speed_hi + i.accel_z + accelerometer_tolerance in

  { speed_lo = lo; speed_hi = hi; }

let estimate_update_accurate (i: inputs) (pre: estimate):
  Lemma
    (requires within_tolerance i.wheel_front i.wheel_rear wheel_tolerance)
    (ensures
        (let e' = estimate_update i pre in
        within_tolerance e'.speed_lo e'.speed_hi wheel_tolerance_speed)) =
  ()

let estimate_update_accuracy_degrades (i: inputs) (pre: estimate) (tol: speed):
  Lemma
    (requires within_tolerance pre.speed_lo pre.speed_hi tol)
    (ensures
        (let e' = estimate_update i pre in
        within_tolerance e'.speed_lo e'.speed_hi (tol + accelerometer_tolerance * 2))) =
  ()


module Exp = Pipit.Exp.Base
module Sugar = Pipit.SugarX4

let previously (e: Sugar.s bool): Sugar.s bool =
  let open Sugar in
  rec' (fun p -> fby false p \/ e)

let count_when_previously (e: Sugar.s bool): Sugar.s int =
  let open Sugar in
  rec' (fun count ->
    let prev = fby 0 count in
    if_then_else e z0 (prev +^ z1)
  )

let previously_n (n: nat) (e: Sugar.s bool): Sugar.s bool =
  let open Sugar in
  previously e /\ count_when_previously e <=^ z n

let veh_speed_estimate (i: Sugar.s inputs): Sugar.s estimate =
  let open Sugar in
  let wheel_front = (fun i -> i.wheel_front) <$> i    in
  let wheel_rear  = (fun i -> i.wheel_rear)  <$> i    in
  let accel_z     = (fun i -> i.accel_z)     <$> i    in
  let wheel_circ  = pure wheel_circ                in
  let z1000       = pure 1000                      in
  let accelerometer_tolerance = pure accelerometer_tolerance in
  let mk_estimate lo hi = (fun lo hi -> { speed_lo = lo; speed_hi = hi }) <$> lo <*> hi in

  let front = (wheel_front *^ wheel_circ) /^ z1000 in
  let rear  = (wheel_rear  *^ wheel_circ) /^ z1000 in
  let min_vel = min <$> front <*> rear             in
  let max_vel = max <$> front <*> rear             in

  let ok    = within_tolerance <$> wheel_front <*> wheel_rear <*> pure wheel_tolerance in

  let lo = rec' (fun lo ->
    if_then_else ok min_vel ((min_vel --> pre lo) +^ accel_z -^ accelerometer_tolerance)) in
  let hi = rec' (fun hi ->
    if_then_else ok max_vel ((max_vel --> pre hi) +^ accel_z +^ accelerometer_tolerance)) in

  let est = mk_estimate lo hi in

  check' "veh_speed_estimate_accurate"
    ((within_tolerance <$> wheel_front <*> wheel_rear <*> pure wheel_tolerance) =>
     (within_tolerance <$> lo <*> hi <*> pure wheel_tolerance_speed)) (
  est)

open Pipit.System.Base
open Pipit.System.Exp
open Pipit.System.Ind
open Pipit.System.Det
module T = FStar.Tactics

// let veh_speed_estimate': system

let run (e: Sugar.s 'a) : Exp.exp [] 'a =
  let (a, _) = e { fresh = 0 } in
  a

let sys =
  system_of_exp (run (veh_speed_estimate (Sugar.m_pure (Exp.XVar (Pipit.Context.Var 100)))))


let prove (fv: sem_freevars): Lemma (ensures base_case (sys fv)) =
  assert (base_case (sys fv)) by (T.norm [primops; iota; delta; zeta; nbe]; T.dump "");
  assert (step_case (sys fv)) by (T.norm [primops; iota; delta; zeta; nbe]; T.dump "")

let dsys': dsystem inputs (bool & speed & speed & prop) estimate =
  {
    init = (true, 0, 0, True);
    step = (fun i (init, lo, hi, chk_accurate) ->
        let front = i.wheel_front * wheel_circ / 1000 in
        let rear  = i.wheel_rear  * wheel_circ / 1000 in
        let min_vel = min front rear                    in
        let max_vel = max front rear                    in

        let ok    = within_tolerance i.wheel_front i.wheel_rear wheel_tolerance in

        let lo' =
            if ok
            then min_vel
            else ((if init then min_vel else lo) + i.accel_z - accelerometer_tolerance)
        in
        let hi' =
            if ok
            then min_vel
            else ((if init then min_vel else hi) + i.accel_z + accelerometer_tolerance)
        in
        let chk_accurate': prop =
          ok ==> within_tolerance lo' hi' wheel_tolerance_speed
        in
        ((false, lo', hi', chk_accurate'),
          { speed_lo = lo'; speed_hi = hi' })
      );
    chck = [("chk_accurate", (fun (_, _, _, c) -> c))];
  }

let sys' = system_of_dsystem dsys'

let prove' (): Lemma (ensures induct1 sys') =
  assert (base_case sys') by (T.norm [primops; iota; delta; zeta; nbe]; T.dump "");
  assert (step_case sys') by (T.norm [primops; iota; delta; zeta; nbe]; T.dump "")
