(* Pipit.Test.Node -- exercise the multi-output node path (TStreamApp / the TLet
   projection idiom).

   Build a source term that instantiates a two-output node with `node`, projects
   its two outputs with `unzip2`, and combines them (`o1 && o2`), lower it to a
   core `tterm`, and check two things by normalisation (everything is closed and
   ground, and `tterm` is an `eqtype`):

     - the lowered term binds each output with its own
       `TLet [B;B] (TStreamApp "ctrl" [true; false]) (TTuple [SBVar i])` -- the
       *same* application duplicated across both outputs, the structural sharing
       a later CSE pass will recover; and

     - the checker types the node application against `EB.benv`, i.e. it looks
       the node up in `env.nodes`, checks the (constant) arguments against the
       parameter binders, and returns its result types. *)
module Pipit.Test.Node

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source
module S   = Pipit.Source.Stream
module EB  = Pipit.Example.Bool
module A   = Pipit.Exp.Anf

let btrue:  PP.pterm = PP.PValue (PR.VBool true)
let bfalse: PP.pterm = PP.PValue (PR.VBool false)

(* Source term:  let (o1, o2) = ctrl(true, false) in o1 && o2.
   The node arguments are constant streams (atoms). `unzip2` projects the two
   outputs (each re-emitting the node application), and `zip2` re-pairs them for
   the lifted `&&`, so the node call ends up duplicated syntactically. *)
let src: S.stream [EB.bool_ty] =
  let (o1, o2) =
    S.unzip2 #EB.bool_ty #[EB.bool_ty]
      (S.node #[EB.bool_ty; EB.bool_ty] #[EB.bool_ty; EB.bool_ty]
        "ctrl" (S.zip2 (S.const btrue) (S.const bfalse)))
  in
  S.liftP PR.PAnd (S.zip2 o1 o2)

let term: PES.tterm = S.exp_of_stream src

(* The shared node application and the expected lowered term. Each output binds
   the node call under its own `TLet`, projecting one component; `zip2` then
   re-binds both projections and `liftP` binds the resulting pair before the
   `&&`. The administrative `TLet`s are the syntactic overhead a later CSE /
   simplification pass folds away (see `anf_shares_node`). *)
let capp: PES.tterm =
  PES.TStreamApp "ctrl" [PES.SPure btrue; PES.SPure bfalse]

let o_proj (i: nat) : PES.tterm =
  PES.TLet [EB.bool_ty; EB.bool_ty] capp (PES.TTuple [PES.SBVar i])

let expected: PES.tterm =
  PES.TLet [EB.bool_ty; EB.bool_ty]
    (PES.TLet [EB.bool_ty] (o_proj 0)
      (PES.TLet [EB.bool_ty] (o_proj 1)
        (PES.TTuple [PES.SBVar 1; PES.SBVar 0])))
    (PES.TTuple [PES.SPureApp PR.PAnd [PES.SBVar 0; PES.SBVar 1]])

(* Lowering emits the two outputs of one (duplicated) node application. *)
let node_lowers_ok (): Lemma (term == expected) =
  assert_norm (term == expected)

(* The checker types the node application: look up `ctrl` in `env.nodes`, check
   the constant arguments against the `BStream` binders, return its results. *)
let node_typechecks (): Lemma (PES.infer_t EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty]) =
  assert_norm (PES.infer_t EB.benv [] capp == Some [EB.bool_ty; EB.bool_ty])

(* ANF lowering recovers the sharing: the node instance -- structurally
   duplicated under both projections in `term` -- collapses into a *single*
   `CLetNode` whose two outputs are referenced by de Bruijn levels 0 and 1, with
   the `and` bound at level 2 and returned.

   `to_anf` is `[@@plugin]`, and this package is checked with `--load_cmxs
   pipit2_plugin` (see the Makefile), so this `assert_norm` reduces `to_anf`
   via its *extracted, compiled* OCaml (a registered native normalizer step),
   not the F* interpreter. This only typechecks because `sigenv` is first-order
   (assoc lists): registering the plugin makes extraction *derive* an `embedding
   sigenv`, and that derivation only composes first-order field embeddings -- it
   has no case for an arrow field. (Reifying a host `_ -> _` back into syntax is
   the hard `'a -> term` direction; the term-to-closure direction is the easy
   one NBE does natively.) *)
let anf_expected: A.cont =
  A.CLetNode "ctrl" [A.APure btrue; A.APure bfalse] [PR.TBool; PR.TBool]
    (A.CLet PR.TBool (A.RPureApp PR.PAnd [A.AVar 0; A.AVar 1])
      (A.CRet [A.AVar 2]))

let anf_shares_node (): Lemma (A.to_anf EB.benv term == Some anf_expected) =
  assert_norm (A.to_anf EB.benv term == Some anf_expected)
