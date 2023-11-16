module Pipit.Norm.Context

open Pipit.Prim.Table

module C = Pipit.Context.Base

(* Definitions can be pure lets, fby, or "free" with no definition. Definitions
  are parameterised by two contexts: `cbound` for the bindings that have a
  value right now -- these bindings can be used anywhere, in pure expressions
  and in follow-by expressions. The second context `ceverything` are the
  bindings that will be bound by later expressions. Only follow-by expressions
  can refer to these bindings, as they will have a value by the time the
  follow-by wants to read them; pure expressions cannot refer to future
  bindings as their value is not available at the time to evaluate the pure
  expression.
*)
type ncontext (t: table) = | NC:
  available: context t ->
  remainder: context t ->
  ncontext t

type ncontext_focus (t: table) = | NCF:
  available: context t ->
  valty:     t.ty ->
  remainder: context t ->
  ncontext_focus t

let ncf_next (#t: table) (ncf: ncontext_focus t): ncontext t =
  NC (ncf.valty :: ncf.available) ncf.remainder

let ncf_prev (#t: table) (ncf: ncontext_focus t): ncontext t =
  NC ncf.available (ncf.valty :: ncf.remainder)

let ncf_available (#t: table) (ncf: ncontext_focus t): context t =
  ncf.available

let ncf_all (#t: table) (ncf: ncontext_focus t): context t =
  C.rev_acc ncf.remainder (ncf.valty :: ncf.available)
  // == C.rev_acc (ncf.valty :: ncf.remainder) ncf.available

let nc_all (#t: table) (nc: ncontext t): context t =
  C.rev_acc nc.remainder nc.available
  // ncf_all ncf == nc_all (ncf_next ncf) == nc_all (ncf_prev ncf)
