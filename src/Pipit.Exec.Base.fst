(* Definition of executable transition systems *)
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

let exec_ap2 (#input #state1 #state2 #result1 #result2: Type)
  (t1: exec input state1 (result1 -> result2))
  (t2: exec input state2 result1):
    exec input (state1 & state2) result2 =
  { init   = (t1.init, t2.init)
  ; eval   = (fun i s ->
    let f  = t1.eval i (fst s) in
    let r2 = t2.eval i (snd s) in
    f r2)
  ; update = (fun i s -> (t1.update i (fst s), t2.update i (snd s)))
  }

let exec_pre (#input #state1 #result1: Type) (r0: result1)
  (t1: exec input state1 result1):
    exec input (state1 * result1) result1 =
  { init = (t1.init, r0)
  ; eval = (fun i s -> snd s)
  ; update = (fun i s -> (t1.update i (fst s), t1.eval i (fst s)))
  }

let exec_then (#input #state1 #state2 #result: Type)
  (t1: exec input state1 result)
  (t2: exec input state2 result):
    exec input (bool * state2) result =
  { init = (true, t2.init)
  ; eval = (fun i s ->
    if fst s
    then t1.eval i t1.init
    else t2.eval i (snd s))
  ; update = (fun i s -> (false, t2.update i (snd s)))
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
  ; eval = (fun i s ->
    let v = t1.eval i (fst s) in
    t2.eval (extend i v) (snd s))
  ; update = (fun i s ->
    let v = t1.eval i (fst s) in
    (t1.update i (fst s), t2.update (extend i v) (snd s)))
  }
