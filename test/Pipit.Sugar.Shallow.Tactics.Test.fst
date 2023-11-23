module Pipit.Sugar.Shallow.Tactics.Test

open Pipit.Sugar.Shallow.Tactics

module SSB = Pipit.Sugar.Shallow.Base


let andb (i j: bool) = i && j
let pairb (i j: bool) = (i, j)
let fstb (i: (bool & bool)) = fst i
let id (#a: eqtype) (i: a) = i
let dup (#a: eqtype) (i: a) = (i, i)
let dup_explicit_strm (#a: eqtype) {| SSB.has_stream a |} (i: a) = (i, i)


%splice[andb_lift] (lift_prim "andb_lift" (`andb))
%splice[pairb_lift] (lift_prim "pairb_lift" (`pairb))
%splice[fstb_lift] (lift_prim "fstb_lift" (`fstb))

%splice[id_lift] (lift_prim "id_lift" (`id))
%splice[dup_lift] (lift_prim "dup_lift" (`dup))

%splice[dup_explicit_strm_lift] (lift_prim "dup_explicit_strm_lift" (`dup_explicit_strm))

%splice[op_AmpAmp; op_BarBar] (lift_prims_named [`Prims.op_AmpAmp; `Prims.op_BarBar])


let test_ty_ok (x: SSB.stream bool): SSB.stream bool = andb_lift (fstb_lift (pairb_lift x x)) x
