module Pipit.Base.Prop.Metadata

[@@plugin]
type prop_status = | PSValid | PSUnknown

type contract_status = prop_status

let contract_status_unknown: contract_status = PSUnknown

type check_mode = prop_status

let prop_status_contains (s: check_mode) (p: prop_status): bool = s = p

let check_mode_valid:   check_mode = PSValid
let check_mode_unknown: check_mode = PSUnknown
