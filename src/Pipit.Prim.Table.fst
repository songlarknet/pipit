(* The primitive table describes the types and primitives operations allowed in
 a Pipit program. The main reason that we declare these explicitly is that we
 want primops and types to have decidable equality. Primitives need decidable
 equality so that we can do common subexpression elimination (CSE) to remove
 duplicate expressions. It's also helpful to have decidable equality on the
 representation of types that occur in the program, because we want to know
 whether a variable reference `x : var t1` is equal to another variable
 reference `y: var t2`, which requires checking if `t1` equals `t2`.

 We could imagine a shallow representation which just reuses types and
 functions from the meta-language. This shallow encoding can be fairly pleasant
 to write programs in, but it's difficult to do deep transforms such as CSE. *)
module Pipit.Prim.Table

type funty (valty: eqtype) =
 | FTVal: t: valty -> funty valty
 | FTFun: t: valty -> rest: funty valty -> funty valty

let rec funty_sem (#typ: eqtype) (typ_sem: typ -> Type) (ft: funty typ) =
  match ft with
  | FTVal t -> typ_sem t
  | FTFun t r -> typ_sem t -> funty_sem typ_sem r

noeq
type table = {
  typ:        eqtype;
  typ_sem:    typ -> eqtype;
  prim:       eqtype;
  prim_types: prim -> funty typ;
  prim_sem:   p: prim -> funty_sem typ_sem (prim_types p);
  // val_eq_dec: t: typ -> a: typ_sem t -> b: typ_sem t -> eq: bool { eq <==> a == b }

  (* Default or bottom: some interpretations of recursive expressions need an
    initial value just to seed the computation, even though the value will
    never be inspected. When we support interesting refinements, we will
    probably only want to provide bottom for unrefined base types. *)
  val_default: t: typ -> typ_sem t
}
