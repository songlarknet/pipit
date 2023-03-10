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

type map2_oracle (value1 value2 oracle1 oracle2: Type) = {
     m2_r1: value1;
     m2_r2: value2;
     m2_o1: oracle1;
     m2_o2: oracle2;
  }

type then_oracle (state1 value2 oracle1 oracle2: Type) = {
     then_s1:  state1;
     then_s1': state1;
     then_r2: value2;
     then_o1: oracle1;
     then_o2: oracle2;
  }


let rec oracle_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> map2_oracle value value (oracle_of_exp e1) (oracle_of_exp e2)
  | XPre e1 -> oracle_of_exp e1
  | XThen e1 e2 -> then_oracle (state_of_exp e1) value (oracle_of_exp e1) (oracle_of_exp e2)
  | XMu e1 -> oracle_of_exp e1

(* An system with "oracles", which let us draw out the quantifiers to the top level *)
let osystem (input: Type) (oracle: Type) (state: Type) (result: Type) = system (input * oracle) state result

(* A system we get from translating an expression *)
let xsystem (e: exp) (vars: nat { wf e vars }) = osystem (C.row vars) (oracle_of_exp e) (state_of_exp e) value

let osystem_input (#input #oracle: Type): osystem input oracle unit input =
  { init = (fun s -> True);
    step = (fun io s s' r -> r == (fst io)) }

let osystem_index (vars: nat) (x: nat { x < vars }):
       osystem (C.row vars) unit unit value =
  { init = (fun _ -> True);
    step = (fun io s s' r ->
      r == C.row_index (fst io) x)
  }

let osystem_map2 (#input #oracle1 #oracle2 #state1 #state2 #value1 #value2 #result: Type) (f: value1 -> value2 -> result)
  (t1: osystem input oracle1 state1 value1)
  (t2: osystem input oracle2 state2 value2):
       osystem input (map2_oracle value1 value2 oracle1 oracle2) (state1 * state2) result =
   {
    init = (fun s -> t1.init (fst s) /\ t2.init (snd s));
    step = (fun io s s' r ->
               let i = fst io in
               let o = snd io in
               t1.step (i, o.m2_o1) (fst s) (fst s') o.m2_r1 /\
               t2.step (i, o.m2_o2) (snd s) (snd s') o.m2_r2 /\
               r == f o.m2_r1 o.m2_r2)
  }

let osystem_pre (#input #oracle1 #state1 #v: Type) (init: v)
  (t1: osystem input oracle1 state1 v):
       osystem input oracle1 (state1 * v) v =
  { init = (fun s -> t1.init (fst s) /\ (snd s) == init);
    step = (fun i s s' r ->
      t1.step i (fst s) (fst s') (snd s') /\ r == (snd s))
  }

let osystem_then (#input #oracle1 #oracle2 #state1 #state2 #v: Type)
  (t1: osystem input oracle1 state1 v)
  (t2: osystem input oracle2 state2 v):
       osystem input (then_oracle state1 v oracle1 oracle2) (bool * state2) v =
  { init = (fun s -> (fst s) = true /\ t2.init (snd s));
    step = (fun io s s' r ->
     let i = fst io in
     let o = snd io in
     if (fst s)
     then t1.init o.then_s1 /\ t1.step (i, o.then_o1) o.then_s1 o.then_s1' r /\ t2.step (i, o.then_o2) (snd s) (snd s') o.then_r2
     else fst s = false /\ t2.step (i, o.then_o2) (snd s) (snd s') r)
  }

let osystem_mu (#input #input' #oracle #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: osystem input' oracle state1 v):
       osystem input  oracle state1 v =
  { init = t1.init;
    step = (fun io s s' r -> t1.step (extend (fst io) r, snd io) s s' r)
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

module Ck = Pipit.Check.Example
module T = FStar.Tactics

open Pipit.System.Ind



let example0_t = osystem_of_exp (Ck.example0_ok Ck.x0) 1

let example0_ok_base (): Lemma (ensures base_case' example0_t) =

  assert (base_case' example0_t) by (
    // T.compute ();
    // T.simpl ();
    // let _ = T.forall_intro_as "x" in
    // let _ = T.forall_intros () in
    T.norm [delta_attr [`%unfold_attr]];
    // T.whnf ();
    // T.unfold_def (`osystem_of_exp);
    // T.l_revert ();
    // T.revert ();
    // T.implies_intro ();
    // T.forall_intro ();
    T.compute ();
    T.dump "base_case"
  );

  ()

let example0_ok_step (): Lemma (ensures step_case' example0_t) =
  assert (step_case' example0_t) by (
    // T.unfold_def (`example0_t);
    // T.norm [delta_attr [`%osystem_of_exp; `%wf]];
    // T.unfold_def (`osystem_of_exp);
    // let _ = T.forall_intros () in
    T.compute ();
    T.dump "step_case");
  ()

let example1_t = osystem_of_exp (Ck.example1_bad Ck.x0) 1

let example1_nok_base (): Lemma (ensures base_case' example1_t) =
  assert (base_case' example1_t) by (T.compute ());
  ()

// this is not true, so we can't prove it
[@@expect_failure]
let example1_nok_step (): Lemma (ensures step_case' example1_t) =
  assert (step_case' example1_t) by (T.compute ());
  ()


// always a => always (always a)
let example_GA_GGA =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    sofar a => sofar (sofar a))
    1

let example_GA_GGA_ok (): unit =
  assert (base_case' example_GA_GGA) by (T.compute ());
  assert (step_case' example_GA_GGA) by (T.compute ());
  ()

// sometimes a => not (always (not a))
let example_F_def =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    once a => Ck.not (sofar (Ck.not a)))
    1

let example_F_def_ok (): unit =
  assert (base_case' example_F_def) by (T.compute ());
  assert (step_case' example_F_def) by (T.compute ());
  ()

// always a /\ always (a => b) => always b
let example_GA_GAB__GB =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    let b = x1 in
    (sofar a /\ sofar (a => b)) => sofar b)
    2

let example_GA_GAB_GB_ok (): unit =
  assert (base_case' example_GA_GAB__GB) by (T.compute (); T.dump "base GA_GAB_GB");
  assert (step_case' example_GA_GAB__GB) by (T.compute (); T.dump "step GA_GAB_GB");
  ()

let example_FA_GAB__FB =
  osystem_of_exp (
    let open Ck in
    let a = x0 in
    let b = x1 in
    (sofar (a => b)) => (once a => once b))
    2

// this seems like it should be true. why can't prove?
let example_GA_GAB_FB_ok (): unit =
  // assert (base_case' example_FA_GAB__FB) by (T.compute (); T.dump "base GA_FAB_FB");
  assert (step_case' example_FA_GAB__FB) by (T.compute (); T.dump "step GA_GAB_FB");
  ()
