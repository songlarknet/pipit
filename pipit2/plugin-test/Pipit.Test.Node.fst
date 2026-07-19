(* Pipit.Test.Node -- exercise the multi-output node path (TStreamApp / the TLet
   projection idiom).

   Build a source term that instantiates a two-output node with `node22` and
   combines its two projected outputs (`o1 && o2`), lower it to a core `tterm`,
   and check two things by normalisation (everything is closed and ground, and
   `tterm` is an `eqtype`):

     - the lowered term binds each output with its own
       `TLet [B;B] (TStreamApp "ctrl" [true; false]) (TTuple [SBVar i])` -- the
       *same* application duplicated across both outputs, the structural sharing
       a later CSE pass will recover; and

     - the checker types the node application against `EB.benv`, i.e. it looks
       the node up in `env.nodes`, checks the (constant) arguments against the
       parameter binders, and returns its result types. *)
module Pipit.Test.Node

module PEB = Pipit.Exp.Base
module S   = Pipit.Source.Stream
module EB  = Pipit.Example.Bool
module A   = Pipit.Exp.Anf

let btrue:  PEB.pterm = PEB.PLit (PEB.LBool true)
let bfalse: PEB.pterm = PEB.PLit (PEB.LBool false)

(* Source term:  let (o1, o2) = ctrl(true, false) in o1 && o2.
   The node arguments are constant streams (atoms), so the two projections carry
   syntactically identical copies of the application. *)
let src: S.stream EB.bool_ty =
  let (o1, o2) =
    S.node22 #EB.bool_ty #EB.bool_ty #EB.bool_ty #EB.bool_ty
      "ctrl" (S.const btrue) (S.const bfalse)
  in
  S.liftP2 EB.p_and o1 o2

let term: PEB.tterm = S.exp_of_stream src

(* The shared node application and the expected lowered term. Each `node22`
   output binds the node call under its own `TLet`, projecting one component; the
   `&&` then binds both outputs. *)
let capp: PEB.tterm =
  PEB.TStreamApp "ctrl" [PEB.SPure btrue; PEB.SPure bfalse]

let o_proj (i: nat) : PEB.tterm =
  PEB.TLet [EB.bool_ty; EB.bool_ty] capp (PEB.TTuple [PEB.SBVar i])

let expected: PEB.tterm =
  PEB.TLet [EB.bool_ty] (o_proj 0)
    (PEB.TLet [EB.bool_ty] (o_proj 1)
      (PEB.TTuple [PEB.SPureApp EB.p_and [PEB.SBVar 1; PEB.SBVar 0]]))

(* Lowering emits the two outputs of one (duplicated) node application. *)
let node_lowers_ok (): Lemma (term == expected) =
  assert_norm (term == expected)

(* The checker types the node application: look up `ctrl` in `env.nodes`, check
   the constant arguments against the `BStream` binders, return its results. *)
let node_typechecks (): Lemma (PEB.infer_t EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty]) =
  assert_norm (PEB.infer_t EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty])

(* ANF lowering recovers the sharing: the node instance -- structurally
   duplicated under both projections in `term` -- collapses into a *single*
   `CLetNode` whose two outputs are referenced by de Bruijn levels 0 and 1, with
   the `and` bound at level 2 and returned.

   `to_anf` is `[@@plugin]`, and this package is checked with `--load_cmxs
   pipit2_plugin` (see the Makefile), so this `assert_norm` reduces `to_anf`
   via its *extracted, compiled* OCaml (a registered native normalizer step),
   not the F* interpreter. This only typechecks because `sigenv` is first-order
   (assoc lists): a function-typed environment cannot be unembedded across the
   native boundary. *)
let anf_expected: A.cont =
  A.CLetNode "ctrl" [A.APure btrue; A.APure bfalse] [PEB.TBool; PEB.TBool]
    (A.CLet PEB.TBool (A.RPureApp EB.p_and [A.AVar 0; A.AVar 1])
      (A.CRet [A.AVar 2]))

let anf_shares_node (): Lemma (A.to_anf EB.benv term == Some anf_expected) =
  assert_norm (A.to_anf EB.benv term == Some anf_expected)
