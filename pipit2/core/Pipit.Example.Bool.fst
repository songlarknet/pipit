(* Pipit.Example.Bool -- a concrete boolean signature environment (`benv`) and a
   first, unverified temporal rewrite rule (`step_sofar_and`, pushing `sofar`
   through `&&`). Design notes and rationale: see Pipit.Example.Bool.md. *)
module Pipit.Example.Bool

module PEB = Pipit.Exp.Base

let bool_ty: PEB.typ = PEB.TBool

let p_and:   PEB.pterm = PEB.PVar "and"
let p_or:    PEB.pterm = PEB.PVar "or"
let p_not:   PEB.pterm = PEB.PVar "not"
let p_sofar: PEB.pterm = PEB.PVar "sofar"

let benv: PEB.sigenv = {
  PEB.prims = [
    "and",   ({ PEB.args = [bool_ty; bool_ty]; result = bool_ty });
    "or",    ({ PEB.args = [bool_ty; bool_ty]; result = bool_ty });
    "not",   ({ PEB.args = [bool_ty];          result = bool_ty });
    "sofar", ({ PEB.args = [bool_ty];          result = bool_ty });
  ];
  PEB.nodes = [
    "ctrl", ({ PEB.params  = [PEB.BStream bool_ty; PEB.BStream bool_ty];
               results = [bool_ty; bool_ty] });
  ];
}

let step_sofar_and (e: PEB.sterm): PEB.sterm =
  match e with
  | PEB.SPureApp (PEB.PVar "sofar") [PEB.SPureApp (PEB.PVar "and") [a; b]] ->
    PEB.SPureApp p_and [PEB.SPureApp p_sofar [a]; PEB.SPureApp p_sofar [b]]
  | _ -> e
