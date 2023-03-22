(* Transition systems *)
module Pipit.System.Base

module C = Pipit.Context

(* Step functions are relations so that we can express non-deterministic systems.
   The recursive dependency for recursive binders XMu is easier to express as a
   relation too. The result type is `prop`, rather than a computational boolean,
   because composing the relations requires existential quantifiers. *)
noeq
type system (input: Type) (state: Type) (result: Type) = {
  init: state -> prop;

  step:
    (* Values of input variables *)
    i: input ->
    (* Starting state *)
    s: state ->
    (* New state *)
    s': state ->
    (* Return value *)
    r: result ->
    prop;
}

let rec system_stepn
  (#outer: nat)
  (#input #state #result: Type)
  (t: system input state result)
  (inputs: C.vector input outer)
  (vs: C.vector result outer)
  (s': state): prop =
  match inputs, vs with
  | [], [] -> t.init s'
  | (row :: inputs'), r :: vs' ->
    exists (s0: state).
    system_stepn #(outer - 1) t inputs' vs' s0 /\
    t.step row s0 s' r

let system_input (#input: Type): system input unit input =
  { init = (fun s -> True);
    step = (fun i s s' r -> r == i) }

let system_const (#input #result: Type) (v: result): system input unit result =
  { init = (fun s -> True);
    step = (fun i s s' r -> r == v) }

let system_map (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: system input state1 value1):
       system input state1 result =
  { init = t1.init;
    step = (fun i s s' r ->
     let s1  = s in
     let s1' = s' in
     exists (r1: value1).
       t1.step i s1 s1' r1 /\
       r == f r1)
  }

let rec system_map_sem (#outer: nat) (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: system input state1 value1)
  (inputs: C.vector input outer)
  (vs: C.vector value1 outer)
  (s': state1):
    Lemma (requires system_stepn t1 inputs vs s')
      (ensures system_stepn (system_map f t1) inputs (C.vector_map f vs) s') =
 match inputs, vs with
 | [], [] -> ()
 | i :: is', v :: vs' ->
   eliminate exists (s0: state1). system_stepn #(outer - 1) t1 is' vs' s0 /\ t1.step i s0 s' v
   returns system_stepn (system_map f t1) inputs (C.vector_map f vs) s'
   with hEx.
        system_map_sem #(outer - 1) f t1 is' vs' s0

let system_map2 (#input #state1 #state2 #value1 #value2 #result: Type) (f: value1 -> value2 -> result)
  (t1: system input state1 value1)
  (t2: system input state2 value2):
       system input (state1 * state2) result =
  {
    init = (fun (s1, s2) -> t1.init s1 /\ t2.init s2);
    step = (fun i (s1, s2) (s1', s2') r ->
     exists (r1: value1) (r2: value2).
               t1.step i s1 s1' r1 /\
               t2.step i s2 s2' r2 /\
               r == f r1 r2)
  }

let system_ite (#input #statep #state1 #state2 #valuep #result: Type) (f: valuep -> bool)
  (tp: system input statep valuep)
  (t1: system input state1 result)
  (t2: system input state2 result):
       system input (statep * state1 * state2) result =
  {
    init = (fun (sp, s1, s2) -> tp.init sp /\ t1.init s1 /\ t2.init s2);
    step = (fun i (sp, s1, s2) (sp', s1', s2') r ->
     exists (rp: valuep) (r1: result) (r2: result).
               tp.step i sp sp' rp /\
               t1.step i s1 s1' r1 /\
               t2.step i s2 s2' r2 /\
               r == (if f rp then r1 else r2))
  }

let system_pre (#input #state1 #v: Type) (init: v)
  (t1: system input state1 v):
       system input (state1 * v) v =
  { init = (fun (s1, v) -> t1.init s1 /\ v == init);
    step = (fun i (s1, v) (s1', v') r ->
      t1.step i s1 s1' v' /\ r == v)
  }

let system_then (#input #state1 #state2 #v: Type)
  (t1: system input state1 v)
  (t2: system input state2 v):
       system input (bool * state2) v =
  { init = (fun (init,s2) -> init = true /\ t2.init s2);
    step = (fun i (init, s2) (init', s2') r ->
     if init
     then exists s1 s1' r'. t1.init s1 /\ t1.step i s1 s1' r /\ t2.step i s2 s2' r' /\ init' = false
     else init' = false /\ t2.step i s2 s2' r)
  }

let system_mu (#input #input' #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: system input' state1 v):
       system input state1 v =
  { init = t1.init;
    step = (fun i s s' r -> t1.step (extend i r) s s' r)
  }

let system_let (#input #input' #state1 #state2 #v1 #v2: Type)
  (extend: input -> v1 -> input')
  (t1: system input  state1 v1)
  (t2: system input' state2 v2):
       system input (state1 * state2) v2 =
  { init = (fun (s1, s2) -> t1.init s1 /\ t2.init s2);
    step = (fun i (s1, s2) (s1', s2') r ->
      exists (r1: v1).
        t1.step i s1 s1' r1 /\
        t2.step (extend i r1) s2 s2' r)
  }
