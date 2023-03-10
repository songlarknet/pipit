(* Transition systems *)
module Pipit.System.ExpX

open Pipit.System.Base

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Causality

module C = Pipit.Context

let rec state_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> state_of_exp e1 * state_of_exp e2
  | XPre e1 -> state_of_exp e1 * value
  | XThen e1 e2 -> bool * state_of_exp e2
  | XMu e1 -> state_of_exp e1

let rec oracle_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> value * value * oracle_of_exp e1 * oracle_of_exp e2
  | XPre e1 -> oracle_of_exp e1
  | XThen e1 e2 -> state_of_exp e1 * state_of_exp e1 * value * oracle_of_exp e1 * oracle_of_exp e2
  | XMu e1 -> oracle_of_exp e1

(* An system with "oracles", which let us draw out the quantifiers to the top level *)
let osystem (input: Type) (oracle: Type) (state: Type) (result: Type) = system (input * oracle) state result

(* A system we get from translating an expression *)
let xsystem (e: exp) (vars: nat { wf e vars }) = osystem (C.row vars) (oracle_of_exp e) (state_of_exp e) value

let osystem_input (#input #oracle: Type): osystem input oracle unit input =
  { init = (fun s -> True);
    step = (fun (i, o) s s' r -> r == i) }

let osystem_index (vars: nat) (x: nat { x < vars }):
       osystem (C.row vars) unit unit value =
  { init = (fun _ -> True);
    step = (fun (i, o) s s' r ->
      r == C.row_index i x)
  }

let osystem_map2 (#input #oracle1 #oracle2 #state1 #state2 #value1 #value2 #result: Type) (f: value1 -> value2 -> result)
  (t1: osystem input oracle1 state1 value1)
  (t2: osystem input oracle2 state2 value2):
       osystem input (value1 * value2 * oracle1 * oracle2) (state1 * state2) result =
   {
    init = (fun (s1, s2) -> t1.init s1 /\ t2.init s2);
    step = (fun (i, (r1, r2, o1, o2)) (s1, s2) (s1', s2') r ->
               t1.step (i, o1) s1 s1' r1 /\
               t2.step (i, o2) s2 s2' r2 /\
               r == f r1 r2)
  }

let osystem_pre (#input #oracle1 #state1 #v: Type) (init: v)
  (t1: osystem input oracle1 state1 v):
       osystem input oracle1 (state1 * v) v =
  { init = (fun (s1, v) -> t1.init s1 /\ v == init);
    step = (fun i (s1, v) (s1', v') r ->
      t1.step i s1 s1' v' /\ r == v)
  }

let osystem_then (#input #oracle1 #oracle2 #state1 #state2 #v: Type)
  (t1: osystem input oracle1 state1 v)
  (t2: osystem input oracle2 state2 v):
       osystem input (state1 * state1 * v * oracle1 * oracle2) (bool * state2) v =
  { init = (fun (init,s2) -> init = true /\ t2.init s2);
    step = (fun (i, (s1, s1', r', o1, o2)) (init, s2) (init', s2') r ->
     if init
     then t1.init s1 /\ t1.step (i, o1) s1 s1' r /\ t2.step (i, o2) s2 s2' r'
     else init = false /\ t2.step (i, o2) s2 s2' r)
  }

let osystem_mu (#input #input' #oracle #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: osystem input' oracle state1 v):
       osystem input  oracle state1 v =
  { init = t1.init;
    step = (fun (i, o) s s' r -> t1.step (extend i r, o) s s' r)
  }

irreducible let unfold_attr = ()

[@@unfold_attr]
let rec osystem_of_exp (e: exp) (vars: nat { wf e vars }):
    xsystem e vars =
  match e with
  | XVal v -> system_const v
  | XVar x -> osystem_index vars x
  | XPrim2 p e1 e2 ->
    osystem_map2 (eval_prim2 p) (osystem_of_exp e1 vars) (osystem_of_exp e2 vars)
  | XPre e1 ->
    osystem_pre xpre_init (osystem_of_exp e1 vars)
  | XThen e1 e2 ->
    osystem_then (osystem_of_exp e1 vars) (osystem_of_exp e2 vars)
  | XMu e1 ->
    let t = osystem_of_exp e1 (vars + 1) in
    osystem_mu #(C.row vars) #(C.row (vars + 1)) (fun i v -> C.row_append (C.row1 v) i) t

// let rec osystem_of_exp_init (e: exp) (vars: nat { wf e vars }) (s: state_of_exp e): prop =
//   match e with
//   | XVal v -> True
//   | XVar x -> True
//   | XPrim2 p e1 e2 ->
//     let ss = s <: state_of_exp e1 * state_of_exp e2 in
//     osystem_of_exp_init e1 vars (fst ss) /\
//     osystem_of_exp_init e2 vars (snd ss)
//   | XPre e1 ->
//     let ss = s <: state_of_exp e1 * value in
//     osystem_of_exp_init e1 vars (fst ss) /\ (snd ss) = xpre_init
//   | XThen e1 e2 ->
//     osystem_then (osystem_of_exp e1 vars) (osystem_of_exp e2 vars)
//   | XMu e1 ->
//     let t = osystem_of_exp e1 (vars + 1) in
//     osystem_mu #(C.row vars) #(C.row (vars + 1)) (fun i v -> C.row_append (C.row1 v) i) t


module Ck = Pipit.Check.Example
module T = FStar.Tactics

open Pipit.System.Ind



let wf_ (): wf_: nat { wf (Ck.example0_ok Ck.x0) wf_ } = 1
let example0_t = osystem_of_exp (Ck.example0_ok Ck.x0) 1

let example0_ok_base (): Lemma (ensures base_case' example0_t) =

  assert (base_case' example0_t) by (
    T.compute ();
    // let _ = T.forall_intros () in
    T.norm [delta_attr [`%unfold_attr]];
    T.whnf ();
    T.unfold_def (`osystem_of_exp);
    // T.l_revert ();
    // T.revert ();
    // T.implies_intro ();
    // T.forall_intro ();
    T.dump "wbase_case"
  );

  admit ()

let example0_ok_step (): Lemma (ensures step_case' example0_t) =
  assert (step_case' example0_t) by (T.compute (); T.dump "step_case");
  ()
