(* Primitive table for shallowly-embedded Pipit.
*)
module Pipit.Prim.Shallow

open Pipit.Prim.Table
// module PR = PipitRuntime.Prim.Bool
module C = Pipit.Context.Base

noeq
type type_table = {
  ty:          Type;
  ty_sem:      ty -> eqtype;
  val_default: t: ty -> ty_sem t;
  propty:      propty: ty { ty_sem propty === bool };
}

noeq
type prim (t: type_table) = {
  prim_id:  option (list string);
  prim_ty:  funty t.ty;
  prim_sem: funty_sem t.ty_sem prim_ty;
}

let axiom_var_eq (t: type_table) (a b: t.ty) (x: C.var a) (x': C.var b):
  Lemma
    (requires C.Var?.v x == C.Var?.v x')
    (ensures a == b /\ x == x') =
  admit ()

let var_eq (t: type_table) (#a #b: t.ty) (x: C.var a) (x': C.var b):
  (eq: bool { eq <==> x === x' }) =
  if C.Var?.v x = C.Var?.v x' then (axiom_var_eq t a b x x'; true) else false

let axiom_prim_eq (t: type_table) (p: prim t { Some? p.prim_id }) (q: prim t { Some? q.prim_id }):
  Lemma
    (requires p.prim_id == q.prim_id)
    (ensures p.prim_ty == q.prim_ty /\
      p.prim_sem == q.prim_sem) =
  admit ()

let prim_eq (t: type_table): eq_dec_partial (prim t) = fun p q ->
  match p.prim_id, q.prim_id with
  | Some p', Some q' ->
    if p' = q'
    then (axiom_prim_eq t p q; true)
    else false
  | _, _ -> false

let table (t: type_table): table = {
   ty          = t.ty;
   ty_sem      = t.ty_sem;
   var_eq      = var_eq t;

   prim        = prim t;
   prim_ty     = (fun (p: prim t) -> p.prim_ty);
   prim_sem    = (fun p -> p.prim_sem);
   prim_eq     = prim_eq t;

   val_default = t.val_default;

   propty      = t.propty;
}
