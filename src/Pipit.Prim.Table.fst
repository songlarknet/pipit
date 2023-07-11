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

let funty (t: eqtype) = list t & t

let rec funty_sem' (#typ: eqtype) (typ_sem: typ -> Type) (args: list typ) (ret: typ) =
  match args with
  | a :: args' -> typ_sem a -> funty_sem' typ_sem args' ret
  | [] -> typ_sem ret

let funty_sem (#typ: eqtype) (typ_sem: typ -> Type) (tys: funty typ) =
  funty_sem' typ_sem (fst tys) (snd tys)

noeq
type table = {
  typ:        eqtype;
  typ_sem:    typ -> Type;
  prim:       eqtype;
  prim_types: prim -> (list typ & typ);
  prim_sem:   (p: prim) -> funty_sem typ_sem (prim_types p);
}
