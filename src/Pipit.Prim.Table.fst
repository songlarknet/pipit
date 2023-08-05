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

let rec funty_sem (#ty: eqtype) (ty_sem: ty -> Type) (ft: funty ty) =
  match ft with
  | FTVal t -> ty_sem t
  | FTFun t r -> (ty_sem t -> funty_sem ty_sem r)

let lemma_funty_sem_FTFun (#ty: eqtype)
  (ty_sem: ty -> Type)
  (a: ty) (b: funty ty):
  Lemma (funty_sem ty_sem (FTFun a b) == (ty_sem a -> funty_sem ty_sem b)) =
  assert_norm (funty_sem ty_sem (FTFun a b) == (ty_sem a -> funty_sem ty_sem b))


noeq
type table: Type u#1 = {
  ty:          eqtype;
  ty_sem:      ty -> eqtype;

  prim:        eqtype;
  prim_ty:     prim -> funty ty;

  prim_sem:    p: prim -> funty_sem ty_sem (prim_ty p);
  // val_eq_dec: t: typ -> a: typ_sem t -> b: typ_sem t -> eq: bool { eq <==> a == b }

  (* Default or bottom: some interpretations of recursive expressions need an
    initial value just to seed the computation, even though the value will
    never be inspected. When we support interesting refinements, we will
    probably only want to provide bottom for unrefined base types. *)
  val_default: t: ty -> ty_sem t;

  // We can't directly embed props because it requires a bigger universe, so
  // instead we describe how to interpret a particular value type as a prop.
  propty:      propty: ty { ty_sem propty === bool };

  // TODO: unit types?
}

(* Helpers for table-parameterised contexts *)
module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

module List = FStar.List.Tot

let context (t: table) = C.context t.ty
let context_sem (c: context 't): C.context eqtype = List.map ('t).ty_sem c

let row (c: context 't) = CR.row (context_sem c)

let lemma_row_index_context_sem
  (#t: table) (c: context t) (x: C.index_lookup c):
  Lemma (t.ty_sem (C.get_index c x) == C.get_index (context_sem c) x)
    [SMTPat (t.ty_sem (C.get_index c x))]
    =
  admit ()

let lemma_drop_context_sem
  (#t: table) (c: context t) (x: C.index_lookup c):
  Lemma (context_sem (C.drop1 c x) == C.drop1 (context_sem c) x)
    [SMTPat (context_sem (C.drop1 c x))]
    =
  admit ()

let lemma_rev_acc_context_sem
  (#t: table) (c c': context t):
  Lemma (context_sem (C.rev_acc c c') == C.rev_acc (context_sem c) (context_sem c'))
    [SMTPat (context_sem (C.rev_acc c c'))]
    =
  admit ()

let lemma_append_context_sem
  (#t: table) (c c': context t):
  Lemma (context_sem (C.append c c') == C.append (context_sem c) (context_sem c'))
    [SMTPat (context_sem (C.append c c'));
     SMTPat (C.append (context_sem c) (context_sem c'))]
    =
  admit ()

// TODO clean
assume val lemma_context_sem_length (t: table) (c: context t):
  Lemma (List.Tot.length (context_sem c) == List.Tot.length c)
    [SMTPat (List.Tot.length (context_sem c))]

assume val lemma_rev_acc_length (c c': C.context 'a):
  Lemma (List.Tot.length (C.rev_acc c c') == List.Tot.length c + List.Tot.length c')
    [SMTPat (List.Tot.length (C.rev_acc c c'))]

assume val lemma_rev_length (c: C.context 'a):
  Lemma (List.Tot.length (List.Tot.rev c) == List.Tot.length c)
    [SMTPat (List.Tot.length (List.Tot.rev c))]

assume val lemma_rev_acc_index_lift (c c': C.context 'a) (i: C.index_lookup c'):
  Lemma (C.get_index (C.rev_acc c c') (i + List.Tot.length c) == C.get_index c' i)

assume val lemma_rev_acc_index_weaken (t: table) (c c': context t) (i: C.index_lookup c):
  Lemma (C.get_index (C.rev_acc c c') i == C.get_index (List.Tot.rev c) i)

// assume val lemma_rev_acc_row_index_lift (t: table) (c c': context t) (i: C.index_lookup c') (r: row c) (r': row c'):
//   Lemma (CR.index _ (CR.rev_acc r r') (i + List.Tot.length c) == CR.index _ r' i)

// assume val lemma_rev_acc_row_index_weaken (t: table) (c c': context t) (i: C.index_lookup c):
//   Lemma (CR.index _ (CR.rev_acc r r') i == CR.index _ (CR.rev r) i)

