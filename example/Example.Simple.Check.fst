module Example.Simple.Check
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Sugar.Shallow.Base

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

(* Unblessed property body from Simple.Check: keep checks, skip proof wrapper.
  The [@@proof_induct1] attribute makes the preprocessor synthesise a
  __check_count_when_prop_body binding that discharges all the [check]s by
  1-induction. *)
[@@proof_induct1]
let count_when_prop_body (e: stream bool): stream unit =
  let count_when_false = count_when false in
  let count_when_e = count_when e in
  let count_when_true = count_when true in
  check (0 <= count_when_false);
  check (count_when_false <= count_when_e);
  check (count_when_e <= count_when_true)

(* Two-argument variant exercising arity-2 of the synthesised __check binding.
  Mirrors Pump.Check.controller_body in shape (two stream-bool inputs). *)
[@@proof_induct1]
let count_when_prop_body2 (e f: stream bool): stream unit =
  let count_when_e = count_when e in
  let count_when_f = count_when f in
  let count_when_true = count_when true in
  check (count_when_e <= count_when_true);
  check (count_when_f <= count_when_true)

(* Negative test: this property is *not* an invariant of count_when
  (count_when e starts at 0, so count_when e > 0 is false at step 0).
  [@@proof_induct1; proof_expect_failure] synthesises a __check binding
  tagged with [@@expect_failure], so the module typechecks iff the check
  fails. *)
[@@proof_induct1; proof_expect_failure]
let count_when_prop_body_fail (e: stream bool): stream unit =
  let count_when_e = count_when e in
  check (count_when_e > 0)

(* Keep rely/guarantee pieces as plain stream predicates for now. *)
let sum_rely (i: stream int): stream bool =
  i > 0

let sum_guarantee (sum i: stream int): stream bool =
  sum > (0 `fby` sum)

(* Unblessed checked-style version of test_sum.
  As above, [@@proof_induct1] auto-generates __check_test_sum_checked_impl. *)
[@@proof_induct1]
let test_sum_checked_impl (i: stream int): stream int =
  let arg = if i > 0 then i else 1 in
  let sarg = sum_impl arg in
  check (sarg > (0 `fby` sarg));
  sarg

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
