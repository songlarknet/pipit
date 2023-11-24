(* Primitive table for shallowly-embedded Pipit.
*)
module Pipit.Prim.Shallow

open Pipit.Prim.Table
module PR  = PipitRuntime.Prim
module C   = Pipit.Context.Base

(* Type of identifiers used as a unique key for types and primitives.
  We assume that the front-end ensures that types with the same identifier are
  equal, and the same for primitives. These assumptions are written as
  axiom_var_eq and axiom_prim_eq below.
  We could use FStar.Reflection.Types.term as the unique key, except that it
  does not have primitive decidable equality. The hand-implemented `term_eq`
  function in FStar.Reflection.V2.TermEq will not reduce `term_eq x x` to true
  when x is some unknown variable, which makes it harder to use in proofs with
  free variables (eg polymorphic definitions).

  For primitives, the identifiers will be used to perform common
  subexpression elimination (CSE). The identifiers need to be unique when they
  are given, but they can be left as None, in which case CSE will not merge
  them with any other operations. CSE is not yet implemented.

  The identifier for types is really just a sanity check: if the front-end
  manages its binders properly then, whenever we compare de Bruijn indices and
  find that they are equal, the types should match. If the front-end is correct
  the values of the type identifiers should never affect the expression.

*)
type ident = list string

noeq
type shallow_type: Type u#1 = {
  ty_id:       ident;
  ty_sem:      eqtype;
  val_default: ty_sem;
}

let funty_sem (t: funty shallow_type): Type0 =
  funty_sem (fun t -> t.ty_sem) t

noeq
type prim: Type u#1 = {
  prim_id:  option ident;
  prim_ty:  funty shallow_type;
  prim_sem: funty_sem prim_ty;
}

let mkPrim
  (prim_id:  option ident)
  (prim_ty:  funty shallow_type)
  (prim_sem: funty_sem prim_ty): prim =
  { prim_id; prim_ty; prim_sem }

let axiom_var_eq (a b: shallow_type) (x: C.var a) (x': C.var b):
  Lemma
    (requires C.Var?.v x == C.Var?.v x' /\ a.ty_id == b.ty_id)
    (ensures a == b /\ x == x') =
  admit ()

let axiom_prim_eq (p: prim { Some? p.prim_id }) (q: prim { Some? q.prim_id }):
  Lemma
    (requires p.prim_id == q.prim_id)
    (ensures p.prim_ty == q.prim_ty /\
      p.prim_sem == q.prim_sem) =
  admit ()

let var_eq (#a #b: shallow_type) (x: C.var a) (x': C.var b):
  (eq: bool { eq <==> x === x' }) =
  if C.Var?.v x = C.Var?.v x' && a.ty_id = b.ty_id then (axiom_var_eq a b x x'; true) else false

let prim_eq: eq_dec_partial prim = fun p q ->
  match p.prim_id, q.prim_id with
  | Some p', Some q' ->
    if p' = q'
    then (axiom_prim_eq p q; true)
    else false
  | _, _ -> false

let bool: shallow_type = {
  ty_id       = [`%Prims.bool];
  ty_sem      = bool;
  val_default = false;
}

let table: table = {
   ty          = shallow_type;
   ty_sem      = (fun t -> t.ty_sem);
   var_eq      = var_eq;

   prim        = prim;
   prim_ty     = (fun (p: prim) -> p.prim_ty);
   prim_sem    = (fun p -> PR.p'delay p.prim_sem);
   prim_eq     = prim_eq;

   val_default = (fun t -> t.val_default);

   propty      = bool;
}
