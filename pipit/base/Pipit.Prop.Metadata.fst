(* Definition of metadata about program properties:
   so far we only distinguish between properties that have already been checked, and those that should be checked.
   In the future we may want admitted properties too (which should be trusted but not checked).
   We probably also want some tracking information like such as source
   locations and the name of the defining function.
*)
module Pipit.Prop.Metadata

(* Status of properties:
   valid:   property that has been verified to hold
   unknown: property that is yet to be verified *)
type prop_status = | PSValid | PSUnknown

(* Status of contracts:
   contract_impl: if PSValid, then implementation has been verified to satisfy guarantees
   contract_env: if PSValid, then environment has been verified to satisfiy relies *)
type contract_status = prop_status

let contract_status_unknown: contract_status = PSUnknown

type check_mode = prop_status

let prop_status_contains (s: check_mode) (p: prop_status): bool =
 s = p

let check_mode_valid:   check_mode = PSValid
let check_mode_unknown: check_mode = PSUnknown

