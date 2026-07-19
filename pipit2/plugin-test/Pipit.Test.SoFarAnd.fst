(* Pipit.Test.SoFarAnd -- end-to-end exercise of the source -> rewrite path.

   Build a source term with the `Stream` combinators (`let'`, a lifted binary
   `&&`, and the `sofar` primitive), lower it to a core `tterm`, run the
   `sofar_and` rewrite over it, and check the result is exactly the expected
   pushed-through term. The equality is decided by normalisation (`tterm` is an
   `eqtype` and everything here is closed and ground), so no proof search is
   needed -- this validates that the combinators, `close`, and the bottom-up
   rewrite driver compose as intended, including rewriting *under* the `let`
   binder. *)
module Pipit.Test.SoFarAnd

module PEB = Pipit.Exp.Base
module S   = Pipit.Source.Stream
module EB  = Pipit.Example.Bool
module RW  = Pipit.Transform.Rewrite

let btrue:  PEB.pterm = PEB.PLit (PEB.LBool true)
let bfalse: PEB.pterm = PEB.PLit (PEB.LBool false)

(* Surface sugar over the boolean environment. *)
let sofar (s: S.stream EB.bool_ty): S.stream EB.bool_ty =
  S.liftP1 EB.p_sofar s

let ( &&. ) (a b: S.stream EB.bool_ty): S.stream EB.bool_ty =
  S.liftP2 EB.p_and a b

(* Source term:  let x = true in sofar (x && false).
   `let'` shares `x` into the body under a single binder. *)
let src: S.stream EB.bool_ty =
  S.let' (S.const btrue) (fun x -> sofar (x &&. S.const bfalse))

(* Lowered core expression. *)
let term: PEB.tterm = S.exp_of_stream src

(* What the rewrite should produce: `sofar` pushed through `&&`, still under the
   `let` binder (so the bound `x` becomes `sofar x`). The single-stream `let'`
   lowers to the n = 1 tuple `TLet`; the whole term is a (width-1) `tterm`, so
   there is no projection wrapper. *)
let expected: PEB.tterm =
  PEB.TLet [EB.bool_ty] (PEB.TTuple [PEB.SPure btrue])
    (PEB.TTuple
      [ PEB.SPureApp EB.p_and
          [ PEB.SPureApp EB.p_sofar [PEB.SBVar 0];
            PEB.SPureApp EB.p_sofar [PEB.SPure bfalse] ] ])

(* The rewrite driver, applied with the `sofar_and` rule, yields `expected`. *)
let sofar_and_ok (): Lemma (RW.rewrite_t EB.step_sofar_and term == expected) =
  assert_norm (RW.rewrite_t EB.step_sofar_and term == expected)
