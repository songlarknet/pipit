(* Transition systems *)
module Pipit.System.Base

module C = Pipit.Context

type xprop = bool

type checks (state: Type) = list (string & (state -> prop))

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

  (* Properties to check *)
  chck: checks state;
}

(* A system with "oracles", which let us draw out the quantifiers to the top level *)
// let osystem (input: Type) (oracle: Type) (state: Type) (result: Type) = system (input & oracle) state result

let map_checks (#state #state': Type) (f: state' -> state) (chck: checks state): checks state' =
  List.Tot.map (fun (name, x) -> (name, (fun s -> x (f s)))) chck

(* Manual instance for universes *)
let app_checks (#state: Type) (chck1 chck2: checks state): checks state =
  List.Tot.append chck1 chck2


let rec system_stepn
  (#input #state #result: Type)
  (t: system input state result)
  (inputs: list (input & result))
  (s': state): prop =
  match inputs with
  | [] -> t.init s'
  | ((row, r) :: inputs') ->
    exists (s0: state).
    system_stepn t inputs' s0 /\
    t.step row s0 s' r

let system_input (#input: Type): system input unit input =
  { init = (fun s -> True);
    step = (fun i s s' r -> r == i);
    chck = [];
  }

let system_const (#input #result: Type) (v: result): system input unit result =
  { init = (fun s -> True);
    step = (fun i s s' r -> r == v);
    chck = [];
  }

// why is this necessary? issue with type inference for prop vs logical
let prop_holds (p: prop): prop = p

let system_check (#input #state: Type) (name: string)
  (t1: system input state xprop):
       system input (xprop & state) xprop =
  { init = (fun (chck, s) -> chck = true /\ t1.init s);
    step = (fun i (_, s) (chck', s') r ->
        t1.step i s s' r /\
        r = chck');
    chck = (name, (fun (chck, s) -> chck == true)) :: map_checks snd t1.chck;
  }

let system_ap2 (#input #state1 #state2 #value1 #value2: Type)
  (t1: system input state1 (value1 -> value2))
  (t2: system input state2 value1):
       system input (state1 & state2) value2 =
  {
    init = (fun (s1, s2) -> t1.init s1 /\ t2.init s2);
    step = (fun i (s1, s2) (s1', s2') r ->
      exists (f: value1 -> value2) (a: value1).
        t1.step i s1 s1' f /\
        t2.step i s2 s2' a /\
        r == f a);
    chck =
      app_checks (map_checks fst t1.chck) (map_checks snd t2.chck);
  }


let system_map (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: system input state1 value1):
       system input state1 result =
  { init = t1.init;
    step = (fun i s s' r ->
      exists (r1: value1).
       t1.step i s s' r1 /\
       r == f r1);
    chck = t1.chck;
  }

let rec system_map_sem (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: system input state1 value1)
  (inputs: list (input & value1))
  (s': state1):
    Lemma (requires system_stepn t1 inputs s')
      (ensures system_stepn (system_map f t1) (List.Tot.map (fun (i,v) -> (i, f v)) inputs) s') =
 match inputs with
 | []  -> ()
 | (i, v) :: is' ->
   eliminate exists (s0: state1). system_stepn t1 is' s0 /\ t1.step i s0 s' v
   returns system_stepn (system_map f t1) (List.Tot.map (fun (i,v) -> (i, f v)) inputs) s'
   with hEx.
        system_map_sem f t1 is' s0

let system_pre (#input #state1 #v: Type) (init: v)
  (t1: system input state1 v):
       system input (state1 & v) v =
  { init = (fun (s1, v) -> t1.init s1 /\ v == init);
    step = (fun i (s1, v) (s1', v') r ->
      t1.step i s1 s1' v' /\ r == v);
    chck = map_checks fst t1.chck;
  }

let system_then (#input #state1 #state2 #v: Type)
  (t1: system input state1 v)
  (t2: system input state2 v):
       system input (bool & state1 & state2) v =
  { init = (fun (init,s1,s2) -> init = true /\ t1.init s1 /\ t2.init s2);
    step = (fun i (init,s1,s2) (init',s1',s2') r ->
     if init
     then exists r'. t1.init s1 /\ t1.step i s1 s1' r /\ t2.step i s2 s2' r' /\ init' = false
     else init' = false /\ t2.step i s2 s2' r);
    chck = app_checks
      // Maybe we could relax this to something like "i ==> s1'" as the check for t1 only needs to hold on the first step...
      (map_checks (fun (i,s1,s2) -> s1) t1.chck)
      (map_checks (fun (i,s1,s2) -> s2) t2.chck);
  }

let system_mu (#input #input' #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: system input' state1 v):
       system input state1 v =
  { init = t1.init;
    step = (fun i s s' r -> t1.step (extend i r) s s' r);
    chck = t1.chck;
  }

let system_let (#input #input' #state1 #state2 #v1 #v2: Type)
  (extend: input -> v1 -> input')
  (t1: system input  state1 v1)
  (t2: system input' state2 v2):
       system input (state1 & state2) v2 =
  { init = (fun (s1, s2) -> t1.init s1 /\ t2.init s2);
    step = (fun i (s1, s2) (s1', s2') r ->
      exists (r1: v1).
        t1.step i s1 s1' r1 /\
        t2.step (extend i r1) s2 s2' r);
    chck = app_checks (map_checks fst t1.chck) (map_checks snd t2.chck);
  }

// TODO UNIMPLEMENTED
let system_contract_instance (#input #input_b #input_ab #state1 #state2 #state3 #a #b: Type)
  (extend_a: input -> b -> input_b)
  (extend_ab: input -> a -> b -> input_ab)
  (assm: system input_b  state1 prop)
  (guar: system input_ab state2 prop)
  (arg:  system input    state3 b):
       system input (state1 & state2 & state3) a =
  { init = (fun (s1, s2, s3) -> assm.init s1 /\ guar.init s2 /\ arg.init s3);
    step = (fun i (s1, s2, s3) (s1', s2', s3') r ->
      exists (rb: b). True);
    chck = [];
  }


let system_bool_holds (#input #state: Type) (t: system input state bool):
  system input state prop =
  system_map (fun b -> prop_holds (b == true)) t
