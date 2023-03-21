module Pipit.Exec.Base

(* Executable transition systems, with separate eval/update phases *)
noeq type exec (input: Type) (state: Type) (result: Type) = {
  init: state;
  eval: input -> state -> result;
  update: input -> state -> state;
}

let exec_input (input: Type): exec input unit input =
  { init   = ()
  ; eval   = (fun i _ -> i)
  ; update = (fun _ _ -> ())}

let exec_const (input #result: Type) (v: result):
  exec input unit result =
  { init   = ()
  ; eval   = (fun _ _ -> v)
  ; update = (fun _ _ -> ())}

let exec_map (#input #state1 #result1 #result2: Type)
  (f: result1 -> result2)
  (t1: exec input state1 result1):
    exec input state1 result2 =
  { init   = t1.init
  ; eval   = (fun i s -> f (t1.eval i s))
  ; update = (fun i s -> t1.update i s)
  }

let exec_map2 (#input #state1 #state2 #result1 #result2 #result3: Type)
  (f: result1 -> result2 -> result3)
  (t1: exec input state1 result1)
  (t2: exec input state2 result2):
    exec input (state1 * state2) result3 =
  { init = (t1.init, t2.init)
  ; eval = (fun i (s1, s2) ->
    let r1 = t1.eval i s1 in
    let r2 = t2.eval i s2 in
    f r1 r2)
  ; update = (fun i (s1, s2) -> (t1.update i s1, t2.update i s2))
  }

let exec_pre (#input #state1 #result1: Type) (r0: result1)
  (t1: exec input state1 result1):
    exec input (state1 * result1) result1 =
  { init = (t1.init, r0)
  ; eval = (fun i (s1, v1) -> v1)
  ; update = (fun i (s1, _) -> (t1.update i s1, t1.eval i s1))
  }

let exec_then (#input #state1 #state2 #result: Type)
  (t1: exec input state1 result)
  (t2: exec input state2 result):
    exec input (bool * state2) result =
  { init = (true, t2.init)
  ; eval = (fun i (iflag, s2) ->
    if iflag
    then t1.eval i t1.init
    else t2.eval i s2)
  ; update = (fun i (_, s2) -> (false, t2.update i s2))
  }

let exec_mu (#input #input' #state1 #result1: Type) (bottom: result1)
  (extend: input -> result1 -> input')
  (t1: exec input' state1 result1):
    exec input state1 result1 =
  { init = t1.init
  ; eval = (fun i s1 -> t1.eval (extend i bottom) s1)
  ; update = (fun i s1 ->
    let r = t1.eval (extend i bottom) s1 in
    t1.update (extend i r) s1)
  }

let exec_let (#input1 #input2 #state1 #state2 #result1 #result2: Type)
  (extend: input1 -> result1 -> input2)
  (t1: exec input1 state1 result1)
  (t2: exec input2 state2 result2):
    exec input1 (state1 * state2) result2 =
  { init = (t1.init, t2.init)
  ; eval = (fun i (s1, s2) ->
    let v = t1.eval i s1 in
    t2.eval (extend i v) s2)
  ; update = (fun i (s1, s2) ->
    let v = t1.eval i s1 in
    (t1.update i s1, t2.update (extend i v) s2))
  }



// let rec exec_map
open Pipit.Exp.Base
module SX = Pipit.System.ExpX
module C = Pipit.Context

let exec_index (vars: nat) (x: nat { x < vars }):
       exec (SX.values_n vars) unit value =
  { init = ()
  ; eval = (fun i s -> SX.values_index vars x i)
  ; update = (fun i s -> ())
  }


let rec state_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> state_of_exp e1 * state_of_exp e2
  | XPre e1 -> state_of_exp e1 * value
  | XThen e1 e2 -> bool * state_of_exp e2
  | XMu e1 -> state_of_exp e1
  | XLet e1 e2 -> state_of_exp e1 * state_of_exp e2

let xexec (e: exp) (vars: nat { wf e vars }) = exec (SX.values_n vars) (state_of_exp e) value

let rec exec_of_exp (e: exp) (vars: nat { wf e vars }): xexec e vars =
  match e with
  | XVal v -> exec_const _ v
  | XVar x -> exec_index vars x
  | XPrim2 p e1 e2 ->
    exec_map2 (eval_prim2 p) (exec_of_exp e1 vars) (exec_of_exp e2 vars)
  | XPre e1 ->
    exec_pre xpre_init (exec_of_exp e1 vars)
  | XThen e1 e2 ->
    exec_then (exec_of_exp e1 vars) (exec_of_exp e2 vars)
  | XMu e1 ->
    exec_mu xpre_init (fun i v -> (v, i)) (exec_of_exp e1 (vars + 1))
  | XLet e1 e2 ->
    exec_let (fun i v -> (v, i)) (exec_of_exp e1 vars) (exec_of_exp e2 (vars + 1))

// module TX = Pipit.Check.Example.TacX

// let eval_x (i: bool) (st: unit * (unit * bool)): bool =
//   let (_, (_, s)) = st in
//   i && s

// let ok (): unit =
//   let open Pipit.Check.Example in

//   assert (exists e. e == eval_x) by
//   // assert (exists e. e == exec_of_exp (sofar x0) 1) by
//     (FStar.Tactics.norm [nbe; primops; iota; zeta; delta]; FStar.Tactics.dump "ok")

//     // (FStar.Tactics.compute (); FStar.Tactics.dump "ok")
//     // (SX.tac_nbe (); FStar.Tactics.dump "ok")
