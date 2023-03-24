(* Translation from expressions to executable transition systems *)
module Pipit.Exec.Exp

open Pipit.Exec.Base
open Pipit.Exp.Base

module C = Pipit.Context

let rec values_n (n: nat): Type =
  match n with
  | 0 -> unit
  | n -> value * values_n (n - 1)

let rec values_index (n: nat) (index: nat { index < n }) (values: values_n n): value =
  match index, values with
  | 0, (v, rest) -> v
  | index, (v, rest) -> values_index (n - 1) (index - 1) rest

let values_cons (n: nat) (v: value) (values: values_n n): values_n (n + 1) = (v, values)

let exec_index (vars: nat) (x: nat { x < vars }):
       exec (values_n vars) unit value =
  { init = ()
  ; eval = (fun i s -> values_index vars x i)
  ; update = (fun i s -> ())
  }

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

let xexec (e: exp) (vars: nat { wf e vars }) = exec (values_n vars) (state_of_exp e) value

noextract inline_for_extraction
let rec exec_of_exp (e: exp) (vars: nat { wf e vars }): xexec e vars =
  match e with
  | XVal v -> exec_const _ v
  | XVar x -> exec_index vars x
  | XPrim2 p e1 e2 ->
    exec_map2 (eval_prim2 p) (exec_of_exp e1 vars) (exec_of_exp e2 vars)
  | XIte ep e1 e2 -> exec_ite (fun v -> v <> 0) (exec_of_exp ep vars) (exec_of_exp e1 vars) (exec_of_exp e2 vars)
  | XPre e1 ->
    exec_pre xpre_init (exec_of_exp e1 vars)
  | XThen e1 e2 ->
    exec_then (exec_of_exp e1 vars) (exec_of_exp e2 vars)
  | XMu e1 ->
    exec_mu xpre_init (fun i v -> values_cons _ v i) (exec_of_exp e1 (vars + 1))
  | XLet e1 e2 ->
    exec_let (fun i v -> values_cons _ v i) (exec_of_exp e1 vars) (exec_of_exp e2 (vars + 1))
