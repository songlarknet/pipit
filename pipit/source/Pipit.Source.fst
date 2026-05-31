module Pipit.Source

// re-export plugin attributes
include Pipit.Plugin.Interface

module PXB = Pipit.Exp.Base
module PSSB = Pipit.Prim.HasStream
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table
module PPL = Pipit.Plugin.Lift
module PSSD = Pipit.Prim.HasStream.Derive

(* Splice [has_stream] instances for single-constructor inductive types. *)
let derive_has_stream = PSSD.derive_has_stream

(* Splice [has_stream] for multi-constructor inductive types; the user
  picks one constructor (by short name) whose application supplies the
  [val_default] value. *)
let derive_has_stream_with_default = PSSD.derive_has_stream_with_default

(*** Public Attributes ***)

(* Do not check properties immediately: defer them for the consumer to check *)
irreducible
let check_defer = ()

(* Prove via k-inductive check *)
irreducible
let check_induct (k: int) = ()

(* Mark to be extracted *)
irreducible
let extract = ()

// plugin preprocesses source to remove mentions of stream type, so we don't need to declare it
// assume new type stream : eqtype -> Type

// define fby primitive by manually lifting
assume val fby (#a: eqtype) {| PSSB.has_stream a |} (dflt: a) (strm: a): a

// LODO getting the mode wrong here leads to some confusing errors - should check it against type of `fby`
[@@core_lifted; core_of_source "Pipit.Source.fby" (ModeFun Static false (ModeFun Static false (ModeFun Static true (ModeFun Stream true Stream))))]
let fby_core (#a: eqtype) {| PSSB.has_stream a |}
  (dflt: a): PXB.exp PPS.table [PSSB.shallow a] (PSSB.shallow a) =
  PXB.XFby dflt (PXB.XBase (PXB.XBVar 0))

assume val check (prop: bool): unit

[@@core_lifted; core_of_source "Pipit.Source.check" (ModeFun Stream true Stream)]
let check_core: PXB.exp PPS.table [PSSB.shallow bool] (PSSB.shallow unit) =
  PXB.XCheck Pipit.Prop.Metadata.PSUnknown (PXB.XBase (PXB.XBVar 0))

(* Hint combinator: instantiate an SMT-pattern-keyed lemma from inside
  a streaming body. Example -- route a monotonicity lemma for [pow2]
  into a streaming check:

     irreducible
     let pow2_monotone_pattern (n m: nat): unit = ()

     let pow2_monotone (n m: nat)
       : Lemma (requires n < m) (ensures pow2 n < pow2 m)
           [SMTPat (pow2_monotone_pattern n m)]
       = FStar.Math.Lemmas.pow2_lt_compat m n

     let body (n m: stream nat): stream unit =
       lemma_pattern (pow2_monotone_pattern n m);
       check ((n <^ m) ==>^ (pow2 n <^ pow2 m))

  The lifted body contains [check (check_pattern (pow2_monotone_pattern
  n m))], so [pow2_monotone_pattern n m] appears as a subterm of the
  SMT query and [pow2_monotone] fires (via its SMTPat) while
  discharging the user's own [check]. The pattern marker MUST be
  [irreducible] or the discharge tactic's normalisation will unfold
  it to [()] and lose the trigger.

  The wrapping through [check_pattern] (rather than just [check (p =
  ())]) is the only encoding we've found that survives the SMT
  encoder: [op_Equality #unit a b] is decidable so the encoder folds
  both sides to [()] and drops the marker subterm. [check_pattern]
  is [assume val] (opaque to the encoder, so the marker survives as
  a trigger candidate) paired with [check_pattern_true] (an SMTPat
  lemma that unconditionally discharges the [check_pattern p = true]
  wrapper obligation). *)

private
assume val check_pattern (pat: unit): bool

private
assume val check_pattern_true (pat: unit)
  : Lemma (check_pattern pat = true) [SMTPat (check_pattern pat)]

[@@source_mode (ModeFun Stream true Stream)]
let lemma_pattern (p: unit): unit =
  check (check_pattern p)
%splice[] (PPL.lift_ast_tac1 "lemma_pattern")

(* Bool implication. The standard F* [==>] is prop-typed (and so cannot
  be auto-lifted by the plugin); use [==>^] instead in #lang-pipit code.
  The caret suffix follows the convention that stream-only operators
  with no prop/F* counterpart are spelled with a trailing [^]. *)
unfold
let op_Equals_Equals_Greater_Hat (a b: bool): bool = if a then b else true


// specialise if-then-else? maybe we should generate better expressions for if-then-else.
// for streaming conditionals, it might be better to generate simple folds functions and reuse them...
// [@@source_mode (ModeFun Static false (ModeFun Static false (ModeFun Stream true (ModeFun Stream true (ModeFun Stream true Stream)))))]
// let if_then_else (#a: eqtype) {| PSSB.has_stream a |} (p: bool) (t f: a): a =
//   if p then t else f

// %splice[] (PPL.lift_ast_tac1 "if_then_else")

// let rec' (#a: eqtype) {| PSSB.has_stream a |} (f: a -> a): a = admit ()

// rec can't currently be implemented here, because the contexts required for rec are a bit weird. instead, it's special-cased in lift_tac
// [@@core_lifted; core_of_source "Plugin.Test.CoreLift.rec'" (ModeFun Static false (ModeFun Static false (ModeFun (ModeFun Stream true Stream) true Stream)))]
// let rec_core (ctx: PPT.context PPS.table) (#a: eqtype) {| PSSB.has_stream a |}
//   (f: PXB.exp PPS.table (PSSB.shallow a :: ctx) (PSSB.shallow a) -> PXB.exp PPS.table (PSSB.shallow a :: ctx) (PSSB.shallow a)): PXB.exp PPS.table ctx (PSSB.shallow a) =
//   PXB.XMu (
//     let x = PXB.XBase (PXB.XBVar 0) in
//     f x)

// TODO check : bool -> unit
// contract?