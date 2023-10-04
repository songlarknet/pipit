(* Translation from expressions to executable transition systems *)
module Pipit.Exec.Exp

open Pipit.Prim.Table
open Pipit.Exp.Base

module Causal = Pipit.Exp.Causality
module SB  = Pipit.System.Base
module SX  = Pipit.System.Exec
module SXE = Pipit.System.Exec.Exp

noextract inline_for_extraction
let state_of_exp_opt (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): option Type =
  SXE.estate_of_exp e

noextract inline_for_extraction
let state_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Type =
  SB.option_type_sem (state_of_exp_opt e)

noextract inline_for_extraction
let extractable (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): bool =
  Causal.causal e

noextract inline_for_extraction
type system (input: Type) (state: option Type) (result: Type) =
  SX.esystem input state result

noextract inline_for_extraction
let exec_of_exp (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a { extractable e }): system (row c) (SXE.estate_of_exp e) (t.ty_sem a) =
  SXE.esystem_of_exp e
