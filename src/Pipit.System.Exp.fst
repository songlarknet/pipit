(* Translation to transition system *)
module Pipit.System.Exp


open Pipit.System.Base

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Causality

module C = Pipit.Context

(* A system we get from translating an expression *)
let xsystem (input: nat) (state: Type) = system (C.row input) state value

let xsystem_stepn
  (#outer #vars: nat)
  (#state: Type)
  (t: xsystem vars state)
  (streams: C.table outer vars)
  (vs: C.vector value outer)
  (s': state): prop =
  let C.Table rs = streams in
  system_stepn t rs vs s'


let rec state_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> state_of_exp e1 * state_of_exp e2
  | XIte ep e1 e2 -> state_of_exp ep * state_of_exp e1 * state_of_exp e2
  | XPre e1 -> state_of_exp e1 * value
  | XThen e1 e2 -> bool * state_of_exp e2
  | XMu e1 -> state_of_exp e1
  | XLet e1 e2 -> state_of_exp e1 * state_of_exp e2

let rec system_of_exp (e: exp) (vars: nat { wf e vars }):
    xsystem vars (state_of_exp e) =
  match e with
  | XVal v -> system_const v
  | XVar x -> system_map (fun i -> C.row_index i x) system_input
  | XPrim2 p e1 e2 ->
    system_map2 (eval_prim2 p) (system_of_exp e1 vars) (system_of_exp e2 vars)
  | XIte ep e1 e2 ->
    system_ite (fun v -> v <> 0) (system_of_exp ep vars) (system_of_exp e1 vars) (system_of_exp e2 vars)
  | XPre e1 ->
    system_pre xpre_init (system_of_exp e1 vars)
  | XThen e1 e2 ->
    system_then (system_of_exp e1 vars) (system_of_exp e2 vars)
  | XMu e1 ->
    let t = system_of_exp e1 (vars + 1) in
    system_mu #(C.row vars) #(C.row (vars + 1)) (fun i v -> C.row_append (C.row1 v) i) t
  | XLet e1 e2 ->
    system_let (fun i v -> C.row_append (C.row1 v) i) (system_of_exp e1 vars) (system_of_exp e2 (vars + 1))

