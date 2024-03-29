(* Normalised systems:

  These describe flat programs, similar to normalised Lustre, where expressions
  are in A-normal form, and follow-by expressions are lifted to top-level
  bindings.
  We can translate from source expressions (Pipit.Exp) in two ways: concrete
  and abstract. Concrete translation is used for executable systems, and any
  contracts are replaced with their implementations. Such systems are totally
  deterministic and should be equivalent to the (concrete) evaluation on source
  expressions. Abstract translation, on the other hand, translates contracts by
  using just their relies and guarantees and ignoring the implementation. These
  systems are not necessarily deterministic, but can be simpler as they hide
  the details of contract implementations. Abstract translation should be an
  abstraction of the concrete evaluation on source expressions.

  refines j k = (forall rows v. rows |- j ↓ v ==> rows |- k ↓ v)

  translate_C e `refines` e `refines` translate_A e
                (or <==>)

  safe (translate_A e) ==> safe (translate_C e)

  What needs doing:
  * definition of norm, norm_defs, expressions, etc
    ✅ norm_defs: fby, pure lets, free/unbound
    ✅ pure non-streaming expressions in ANF
    - norm_det, deterministic variant, which disallows 'FREE' definitions
  * semantics of norm: total, non-deterministic;
    ✅ expressions can be function
    ✅ norm_defs is relation
    - system is relation
    - deterministic if no frees
  * translation from exp:
    - concrete translate_C uses implementations
    - abstract translate_A uses contracts
    - corectness proofs, invariants
  * norm combinators
    - union, applicative functor
  * norm operations:
    - lifting expressions etc
  * cse/gvn/sharing recovery:
    - correctness needs <==>: different directions required for abstract vs contract
  * statement of contracts:
    - exp wants to state contract as something like:
      contract_witness (arg: Type) (res: Type)
        (rely: norm [arg]      bool)
        (guar: norm [arg, res] bool)
        (impl: norm [arg]      res) =
        forall (rows: list (row arg)).
          rows |- ALWAYS rely ==>
          rows, impl(rows) |- ALWAYS guar

      (is this equivalent to ALWAYS rely /\ PREVIOUSLY (ALWAYS guar) => guar)?

  * translation to existential LTS:
    - for proofs
    - correctness proof should be relatively easy, only needs one way
  * translation to executable systems:
    - correctness proof, eventually?

  Problems:
  * CSE/GVN cannot remove duplicate occurrences of the same contract.
    This should be less of an issue once the front-end sugar is using effects
    because things won't be duplicated by default.
*)
module Pipit.Norm

include Pipit.Norm.Defs

open Pipit.Prim.Table

let norm_contract_prop
  (#t: table) (#valty #argty: t.ty)
  (rely: norm_det t [argty]        t.propty)
  (guar: norm_det t [argty; valty] t.propty)
  (impl: norm_det t [argty]        valty): prop =
 True
//  (forall (args: list (row argty)).
//    norm_det_always args rely ==>
//    norm_det_always (row_zip2 r (norm_det_sems args impl)) guar)

type norm_contract (t: table) (valty argty: t.ty) = {
  rely: norm_det t [argty]        t.propty;
  guar: norm_det t [argty; valty] t.propty;
  impl: norm_det t [argty]        valty;
  wit:  norm_contract_prop rely guar impl;
}

let norm_contract_sem
  (#t: table) (#valty #argty: t.ty)
  (streams: list (t.ty_sem argty))
  (c: norm_contract t valty argty):
    t.ty_sem valty =
  admit ()
