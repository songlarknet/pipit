(* Translation from expressions to executable transition systems *)
module Pipit.Exec.Exp

open Pipit.Prim.Table
open Pipit.Exp.Base

module Causal = Pipit.Exp.Causality
module SD = Pipit.System.Det
module SE = Pipit.System.Exp

noextract inline_for_extraction
let state_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Type =
  SE.dstate_of_exp e

noextract inline_for_extraction
let extractable (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): bool =
  Causal.causal e

noextract inline_for_extraction
type system (input state result: Type) =
  SD.dsystem input state result

noextract inline_for_extraction
let exec_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a { extractable e }): system (row c) (state_of_exp e) (t.ty_sem a) =
  SE.dsystem_of_exp e
