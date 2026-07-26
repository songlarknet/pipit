module Pipit.Core.Example.Bool

module PR  = Pipit.Core.Exp.Prim
module PES = Pipit.Core.Exp.Source

let bool_ty: PR.typ = PR.TBool

let benv: PES.sigenv = {
  PES.nodes = [
    ("ctrl",  { PES.params  = [PES.BStream bool_ty; PES.BStream bool_ty];
                results = [bool_ty; bool_ty]; body = None });
    ("sofar", { PES.params  = [PES.BStream bool_ty];
                results = [bool_ty]; body = None });
  ];
}
