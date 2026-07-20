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
