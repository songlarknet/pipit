(* A small example signature environment over the boolean type: two multi-output
   nodes, `ctrl` and the temporal `sofar`. The boolean *operators* (`and`, `or`,
   `not`) are built-in primitives (`Pipit.Exp.Prim`), so they need no signature
   here; `sofar` is genuinely a node -- a recursive stream definition -- and is
   registered as such. Design notes and rationale: see Pipit.Example.Bool.md. *)
module Pipit.Example.Bool

module PR  = Pipit.Exp.Prim
module PES = Pipit.Exp.Source

let bool_ty: PR.typ = PR.TBool

let benv: PES.sigenv = {
  PES.nodes = [
    ("ctrl",  { PES.params  = [PES.BStream bool_ty; PES.BStream bool_ty];
                results = [bool_ty; bool_ty] });
    ("sofar", { PES.params  = [PES.BStream bool_ty];
                results = [bool_ty] });
  ];
}
