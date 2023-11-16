(* Definition of metadata about program properties:
   so far we only distinguish between properties that have already been checked, and those that should be checked.
   In the future we may want admitted properties too (which should be trusted but not checked). *)
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

(* set of prop_status
   The definition of "checking" a property is parameterised by which kinds of properties one is interested in.
   It helps to have a first-order representation of a set of property kinds.
 *)
type prop_status_set = {
  prop_status_valid:   bool;
  prop_status_unknown: bool;
}

let prop_status_contains (s: prop_status_set) (p: prop_status): bool =
 match p with
 | PSValid   -> s.prop_status_valid
 | PSUnknown -> s.prop_status_unknown

type check_mode = prop_status_set
// type check_mode = {
//   check_set:           prop_status_set;
//   check_contract_impl: prop_status_set;
//   check_contract_env:  prop_status_set;
// }

let check_mode_none:    check_mode = { prop_status_valid = false; prop_status_unknown = false; }
let check_mode_valid:   check_mode = { prop_status_valid = true;  prop_status_unknown = false; }
let check_mode_unknown: check_mode = { prop_status_valid = false; prop_status_unknown = true; }
let check_mode_all:     check_mode = { prop_status_valid = true;  prop_status_unknown = true; }
