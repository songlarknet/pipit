(* Executable transition systems.
  The abstract transition systems in Pipit.System have some extra parts such
  as the oracle/free context and the proof obligations and assumptions. We
  don't need them for executable systems, so this is a bare-bones
  transition system that is simpler for generating code.
*)
module Pipit.System.Exec

open Pipit.System.Base

module List = FStar.List.Tot

(*** Systems ***)
noeq
type esystem (input: Type) (state: option Type) (result: Type) = {
  init: option_type_sem state;

  step:
    (* Values of input variables *)
    i: input ->
    (* Starting state *)
    s: option_type_sem state ->
    (* Updated state and result *)
    (option_type_sem state & result);
}

(*** Semantics ***)

(* Semantics of executing a transition system *)
let rec esystem_steps
  (#input #result: Type)
  (#state: option Type)
  (t: esystem input state result)
  (inputs: list input):
    (option_type_sem state & r: list result { List.length r == List.length inputs }) =
  match inputs with
  | [] -> (t.init, [])
  | i :: inputs' ->
    let (s, rs) = esystem_steps t inputs' in
    let (s', v) = t.step i s in
    (s', v :: rs)

(*** Combinators ***)
noextract inline_for_extraction
let esystem_const (#input #result: Type) (v: result): esystem input None result =
  { init = ();
    step = (fun i s -> ((), v));
  }

noextract inline_for_extraction
let esystem_project (#input #result: Type) (f: input -> result):
       esystem input None result =
  { init = ();
    step = (fun i s -> ((), f i));
  }

noextract inline_for_extraction
let esystem_with_input (#input #input' #result: Type) (#state: option Type) (f: input' -> input)
    (t: esystem input state result):
        esystem input' state result =
  { init = t.init;
    step = (fun i s -> t.step (f i) s);
  }

noextract inline_for_extraction
let esystem_pre (#input #v: Type) (#state1: option Type) (init: v)
  (t1: esystem input state1 v):
       esystem input (Some v `type_join` state1) v =
  { init = type_join_tup init t1.init;
    step = (fun i s ->
      let (s1', v') = t1.step i (type_join_snd s) in
      (type_join_tup v' s1', type_join_fst s));
  }

noextract inline_for_extraction
let esystem_mu_causal (#input #input' #v: Type)
  (#state1: option Type)
  (bottom: v)
  (extend: input -> v -> input')
  (t1: esystem input' state1 v):
       esystem input state1 v =
  { init = t1.init;
    step = (fun i s ->
      let (_, r) = t1.step (extend i bottom) s in
      // r is used twice, so don't inline it into both occurrences
      [@@no_inline_let]
      let r = r in
      let (s',_) = t1.step (extend i      r) s in
      (s', r));
  }

noextract inline_for_extraction
let esystem_let (#input #input' #v1 #v2: Type)
  (#state1 #state2: option Type)
  (extend: input -> v1 -> input')
  (t1: esystem input  state1 v1)
  (t2: esystem input' state2 v2):
       esystem input (state1 `type_join` state2) v2 =
  { init = type_join_tup t1.init t2.init;
    step = (fun i s ->
      let (s1', r1) = t1.step i (type_join_fst s) in
      let (s2', r2) = t2.step (extend i r1) (type_join_snd s) in
      (type_join_tup s1' s2', r2));
  }

noextract inline_for_extraction
let esystem_let_no_inline (#input #input' #v1 #v2: Type)
  (#state1 #state2: option Type)
  (extend: input -> v1 -> input')
  (t1: esystem input  state1 v1)
  (t2: esystem input' state2 v2):
       esystem input (state1 `type_join` state2) v2 =
  { init = type_join_tup t1.init t2.init;
    step = (fun i s ->
      let (s1', r1) = t1.step i (type_join_fst s) in
      // we don't want to inline the value r1 into its use site, because if
      // it is mentioned multiple times it will duplicate work
      [@@no_inline_let]
      let r1 = r1 in
      let (s2', r2) = t2.step (extend i r1) (type_join_snd s) in
      (type_join_tup s1' s2', r2));
  }

noextract inline_for_extraction
let esystem_unit_state (#input #result: Type)
    (t: esystem input None result):
        esystem input (Some unit) result =
  { init = ();
    step = (fun i (s: option_type_sem (Some unit)) ->
      let (_, v) = t.step i () in
      ((), v));
  }
