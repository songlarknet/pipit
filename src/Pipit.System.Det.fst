(* Deterministic transition systems *)
module Pipit.System.Det

open Pipit.System.Base

(* Deterministic systems can't express the whole language, but they can do a subset of it much simpler *)
noeq
type dsystem (input: Type) (state: Type) (result: Type) = {
  init: state;

  step:
    (* Values of input variables *)
    i: input ->
    (* Starting state *)
    s: state ->
    (* Updated state and result *)
    (state & result);

  (* Properties to check *)
  chck: checks state;
}

let system_of_dsystem
  (#input #state #result: Type)
  (t: dsystem input state result):
       system input state result =
  { init = (fun s -> s == t.init);
    step = (fun i s s' r ->
      (s', r) == t.step i s);
    chck = t.chck;
  }

let dsystem_input (#input: Type): dsystem input unit input =
  { init = ();
    step = (fun i s -> ((), i));
    chck = [];
  }

let dsystem_const (#input #result: Type) (v: result): dsystem input unit result =
  { init = ();
    step = (fun i s -> ((), v));
    chck = [];
  }

let dsystem_check (#input #state: Type) (name: string)
  (t1: dsystem input state xprop):
       dsystem input (xprop & state) xprop =
  { init = (true, t1.init);
    step = (fun i s ->
        let (s2', r) = t1.step i (snd s) in
        ((r, s2'), r));
    chck = (name, (fun s -> fst s == true)) :: map_checks snd t1.chck;
  }

let dsystem_ap2 (#input #state1 #state2 #value1 #value2: Type)
  (t1: dsystem input state1 (value1 -> value2))
  (t2: dsystem input state2 value1):
       dsystem input (state1 & state2) value2 =
  {
    init = (t1.init, t2.init);
    step = (fun i s ->
        let (s1', f) = t1.step i (fst s) in
        let (s2', a) = t2.step i (snd s) in
        ((s1', s2'), f a));
    chck =
      app_checks (map_checks fst t1.chck) (map_checks snd t2.chck);
  }

let dsystem_map (#input #state1 #value1 #value2: Type)
  (f: value1 -> value2)
  (t1: dsystem input state1 value1):
       dsystem input state1 value2 =
  {
    init = t1.init;
    step = (fun i s1 ->
        let (s1', a) = t1.step i s1 in
        (s1', f a));
    chck = t1.chck;
  }


let dsystem_pre (#input #state1 #v: Type) (init: v)
  (t1: dsystem input state1 v):
       dsystem input (state1 & v) v =
  { init = (t1.init, init);
    step = (fun i s ->
      let (s1', v') = t1.step i (fst s) in
      ((s1', v'), snd s));
    chck = map_checks fst t1.chck;
  }

let dsystem_then (#input #state1 #state2 #v: Type)
  (t1: dsystem input state1 v)
  (t2: dsystem input state2 v):
       dsystem input (system_then_state state1 state2) v =
  { init = ({ init = true; s1 = t1.init; s2 = t2.init; } <: system_then_state state1 state2);
    step = (fun i (s: system_then_state state1 state2) ->
     let init = s.init in
     let s1 = s.s1 in
     let s2 = s.s2 in
     let (s1', v1) = t1.step i s1 in
     let (s2', v2) = t2.step i s2 in
     let s' = { init = false; s1 = s1'; s2 = s2' } <: system_then_state state1 state2 in
     (s', (if init then v1 else v2)));
    chck = app_checks
      (map_checks (fun s -> s.s1) t1.chck)
      (map_checks (fun s -> s.s2) t2.chck);
  }

let dsystem_mu_causal (#input #input' #state1 #v: Type)
  (bottom: v)
  (extend: input -> v -> input')
  (t1: dsystem input' state1 v):
       dsystem input state1 v =
  { init = t1.init;
    step = (fun i s ->
      let (s',r) = t1.step (extend i bottom) s in
      t1.step (extend i r) s);
    chck = t1.chck;
  }

let dsystem_let (#input #input' #state1 #state2 #v1 #v2: Type)
  (extend: input -> v1 -> input')
  (t1: dsystem input  state1 v1)
  (t2: dsystem input' state2 v2):
       dsystem input (state1 & state2) v2 =
  { init = (t1.init, t2.init);
    step = (fun i s ->
      let (s1', r1) = t1.step i (fst s) in
      let (s2', r2) = t2.step (extend i r1) (snd s) in
      ((s1', s2'), r2));
    chck = app_checks (map_checks fst t1.chck) (map_checks snd t2.chck);
  }

