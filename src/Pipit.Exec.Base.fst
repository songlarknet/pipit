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

let exec_ite (#input #state1 #state2 #state3 #cond #result: Type)
  (f: cond -> bool)
  (t1: exec input state1 cond)
  (t2: exec input state2 result)
  (t3: exec input state3 result):
    exec input (state1 * state2 * state3) result =
  { init = (t1.init, t2.init, t3.init)
  ; eval = (fun i (s1, s2, s3) ->
    let r1 = t1.eval i s1 in
    let r2 = t2.eval i s2 in
    let r3 = t3.eval i s3 in
    if f r1 then r2 else r3)
  ; update = (fun i (s1, s2, s3) -> (t1.update i s1, t2.update i s2, t3.update i s3))
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
