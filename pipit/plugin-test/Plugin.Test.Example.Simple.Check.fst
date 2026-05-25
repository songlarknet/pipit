module Plugin.Test.Example.Simple.Check
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PXB  = Pipit.Exp.Base
module PXCB = Pipit.Exp.Checked.Base
module SI   = Pipit.System.Ind
module SX   = Pipit.System.Exp
module PT   = Pipit.Tactics

instance has_stream_int: PSSB.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

(* Count the number of times a predicate has been true. *)
let count_when (p: stream bool): stream int =
  let rec count =
    (0 `fby` count) + (if p then 1 else 0)
  in
  count

(* Unchecked implementation version of the sum stream from Simple.Check. *)
let sum_impl (i: stream int): stream int =
  let rec sum = (0 `fby` sum) + i in
  sum

(* Unchecked implementation version of test_sum from Simple.Check. *)
let test_sum_impl (i: stream int): stream int =
  let arg = if i > 0 then i else 1 in
  sum_impl arg

(* Unblessed property body from Simple.Check: keep checks, skip proof wrapper. *)
let count_when_prop_body (e: stream bool): stream unit =
  let count_when_false = count_when false in
  let count_when_e = count_when e in
  let count_when_true = count_when true in
  check (0 <= count_when_false);
  check (count_when_false <= count_when_e);
  check (count_when_e <= count_when_true)

(* Blessed version of count_when_prop_body: verify all [check]s by induction. *)
[@@core_of_source (`%count_when_prop_body) (ModeFun Stream true Stream)]
let count_when_prop_body_check
  : PXB.exp PPS.table [PSSB.shallow bool] (PSSB.shallow unit) =
  let unfold e = __core_count_when_prop_body in
  let unfold sys = SX.system_of_exp e in
  assert (SI.induct1 sys) by (PT.norm_full []);
  PXCB.bless e

(* Keep rely/guarantee pieces as plain stream predicates for now. *)
let sum_rely (i: stream int): stream bool =
  i > 0

let sum_guarantee (sum i: stream int): stream bool =
  sum > (0 `fby` sum)

(* Unblessed checked-style version of test_sum. *)
let test_sum_checked_impl (i: stream int): stream int =
  let arg = if i > 0 then i else 1 in
  let sarg = sum_impl arg in
  check (sarg > (0 `fby` sarg));
  sarg

(* Blessed version of test_sum_checked_impl. Mirrors test_sum_ in Simple.Check. *)
[@@core_of_source (`%test_sum_checked_impl) (ModeFun Stream true Stream)]
let test_sum_checked_impl_check
  : PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int) =
  let unfold e = __core_test_sum_checked_impl in
  let unfold sys = SX.system_of_exp e in
  assert (SI.induct1 sys) by (PT.norm_full []);
  PXCB.bless e

(* From Simple.Check, but kept as a plain predicate (no contract proof yet). *)
let times_guarantee (x y z: stream int): stream bool =
  let abs_x = abs x in
  let abs_y = abs y in
  let abs_z = abs z in
  ((z = y) = ((x = 1) || (y = 0))) &&
  ((z = x) = ((y = 1) || (x = 0))) &&
  ((z = 0) = ((x = 0) || (y = 0))) &&
  ((z > 0) = (((x > 0) && (y > 0)) || ((x < 0) && (y < 0)))) &&
  ((z < 0) = (((x > 0) && (y < 0)) || ((x < 0) && (y > 0)))) &&
  ((abs_z >= abs_y) = ((abs_x >= 1) || (y = 0))) &&
  ((abs_z >= abs_x) = ((abs_y >= 1) || (x = 0))) &&
  ((abs_z <= abs_y) = ((abs_x <= 1) || (y = 0))) &&
  ((abs_z <= abs_x) = ((abs_y <= 1) || (x = 0)))
