(* `#lang-pipit` exercise of the `Stream <ret> (requires R) (ensures G)`
   return-type sugar. The preprocessor splits

     let body (x: stream int): Stream int
       (requires x >= 0)
       (ensures fun r -> r > 0)
       = x + 1

   into three plain `#lang-pipit` bindings (body_rely, body_guar,
   body) plus the same `proof_contract` attribute on the body that
   `Plugin.Test.Core.Contract` writes by hand. The downstream
   `core_of_source` / `bless_contract` / `find_core_for_source`
   machinery is unchanged.

   Mirrors `Plugin.Test.Core.Contract`'s good/bad caller pair. *)
module Plugin.Test.Source.Contract
#lang-pipit

open Pipit.Source

let body (x: stream int): Stream int
  (requires x >= 0)
  (ensures fun r -> r > 0)
  = x + 1

(* Positive caller: passing `1` satisfies the rely. *)
[@@proof_induct1]
let good_caller (_x: stream int): stream int =
  body 1

(* Negative caller: passing `-1` violates the rely; we expect the
   spliced check to fail. *)
[@@proof_induct1; proof_expect_failure]
let bad_caller (_x: stream int): stream int =
  body (-1)
