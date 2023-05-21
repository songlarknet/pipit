(* Inductive proofs on transition systems *)
module Pipit.System.Ind

open Pipit.System.Base

module C = Pipit.Context

let rec prop_for_all (l: list prop): prop =
 match l with
 | [] -> True
 | p :: ps -> p /\ prop_for_all ps

let all_checks_hold (#input #state #value: Type) (t: system input state value) (s: state): prop =
  prop_for_all (List.Tot.map (fun (n, i) -> i s) t.chck)

let system_holds (#input #state #value: Type) (t: system input state value): prop =
  forall (inputs: list (input & value)) (s: state).
    Cons? inputs            ==>
    system_stepn t inputs s ==>
    all_checks_hold t s

let base_case (#input #state #value: Type) (t: system input state value): prop =
  forall (i: input) (s: state) (s': state) (r: value).
    t.init s ==> t.step i s s' r ==>
    all_checks_hold t s'

let rec base_case_k' (k: nat) (#input #state #value: Type) (t: system input state value) (s': state) (check: prop): prop =
  match k with
  | 0 -> t.init s' ==> check
  | _ ->
    forall (i: input) (s: state) (r: value).
      t.step i s s' r ==>
      base_case_k' (k - 1) t s check

let rec base_case_k (k: nat) (#input #state #value: Type) (t: system input state value): prop =
  (if k > 1 then base_case_k (k - 1) t else True) /\
  (forall (s': state). base_case_k' k t s' (all_checks_hold t s'))

let step_case (#input #state #value: Type) (t: system input state value): prop =
  forall (i0 i1: input) (s0: state) (s1 s2: state) (r0 r1: value).
    t.step i0 s0 s1 r0 ==> all_checks_hold t s1 ==>
    t.step i1 s1 s2 r1 ==> all_checks_hold t s2

let rec step_case_k' (k: nat) (#input #state #value: Type) (t: system input state value) (s': state) (check: prop): prop =
  match k with
  | 0 -> check
  | _ -> forall (i: input) (s: state) (r: value).
    t.step i s s' r ==>
    all_checks_hold t s ==>
    step_case_k' (k - 1) t s check

let step_case_k (k: nat) (#input #state #value: Type) (t: system input state value): prop =
  forall (s': state). step_case_k' k t s' (all_checks_hold t s')

let induct1 (#input #state #value: Type)
  (t: system input state value): prop =
    base_case t /\ step_case t

let rec induct1_sound' (#input #state #value: Type)
  (t: system input state value)
  (inputs: list (input & value))
  (s': state):
    Lemma
        (requires system_stepn t inputs s' /\ induct1 t /\ Cons? inputs)
        (ensures all_checks_hold t s')
        (decreases inputs) =
  match inputs with
  | [] -> ()
  | [(i, v)] -> ()
  | (i1,v1) :: (i0,v0) :: ivs ->
    eliminate exists (s0: state) (s1: state).
      system_stepn t ivs s0 /\
      t.step i0 s0 s1 v0 /\
      t.step i1 s1 s' v1
    returns all_checks_hold t s'
    with h.
      (induct1_sound' t ((i0, v0) :: ivs) s1)

let induct1_sound (#input #state #value: Type)
  (t: system input state value):
    Lemma
        (requires induct1 t)
        (ensures system_holds t) =
  introduce forall (inputs: list (input & value) { Cons? inputs }) (s: state { system_stepn t inputs s }).
    (Cons? inputs) ==>
    system_stepn t inputs s ==>
    all_checks_hold t s
  with
    (induct1_sound' t inputs s)

let induct_k (k: nat) (#input #state #value: Type)
  (t: system input state value): prop =
    base_case_k k t /\ step_case_k k t

let rec induct2_sound' (#input #state #value: Type)
  (t: system input state value)
  (inputs: list (input & value))
  (s': state):
    Lemma
        (requires system_stepn t inputs s' /\ induct_k 2 t)
        (ensures Nil? inputs \/ all_checks_hold t s')
        (decreases inputs) =
  match inputs with
  | [] -> ()
  | [(i0, v0)] -> ()
  | [(i0, v0); (i1, v1)] -> ()
  | (i2,v2) :: (i1,v1) :: (i0,v0) :: ivs ->
    eliminate exists (s0: state) (s1: state) (s2: state).
      system_stepn t ivs s0 /\
      t.step i0 s0 s1 v0 /\
      t.step i1 s1 s2 v1 /\
      t.step i2 s2 s' v2
    returns all_checks_hold t s'
    with h.
      (induct2_sound' t ((i1, v1) :: (i0, v0) :: ivs) s2;
      induct2_sound' t ((i0, v0) :: ivs) s1;
      ())

let induct2_sound (#input #state #value: Type)
  (t: system input state value):
    Lemma
        (requires induct_k 2 t)
        (ensures system_holds t) =
  introduce forall (inputs: list (input & value) { Cons? inputs }) (s: state { system_stepn t inputs s }).
    (Cons? inputs) ==>
    system_stepn t inputs s ==>
    all_checks_hold t s
  with
    (induct2_sound' t inputs s)

// TODO inductk_sound

(* Shelved: proof that properties proved for transition systems apply to original expression *)
// open Pipit.Exp.Base
// open Pipit.Exp.Bigstep
// open Pipit.Exp.Causality

// open Pipit.System.Exp

// let exp_valid (e: exp) (vars: nat) = wf e vars /\ causal e

// let exp_for_all (e: exp) (vars: nat): prop =
//   forall (len: nat)
//     (inputs: C.table len vars)
//     (vs: C.vector value len)
//     (hBS: bigstep inputs e vs).
//     List.Tot.for_all (fun r -> r <> 0) vs

// let prop_of_value (v: value): prop = ~ (v = 0)

// let rec prop_for_all__prop_of_bool (vs: list value):
//   Lemma (requires prop_for_all (C.vector_map #(List.Tot.length vs) prop_of_value vs))
//         (ensures List.Tot.for_all (fun r -> r <> 0) vs) =

// let induct1_exp (#vars: nat)
//   (e: exp { exp_valid e vars }):
//   Lemma (requires induct1 (system_map prop_of_value (system_of_exp e vars)))
//         (ensures exp_for_all e vars) =
//   introduce forall (len: nat) (inputs: C.vector (C.row vars) len) (vs: C.vector bool len) (hBS: bigstep (C.Table inputs) e vs). List.Tot.for_all (fun r -> r) vs
//   with
//   begin
//     system_eval_complete e (C.Table inputs) vs hBS;
//     eliminate exists (s': (state_of_exp e)). system_stepn (system_of_exp e vars) inputs vs s'
//     returns _
//     with hEx.
//     begin
//         system_map_sem prop_of_bool (system_of_exp e vars) inputs vs s';
//         induct1_sound (system_map prop_of_bool (system_of_exp e vars)) inputs (C.vector_map prop_of_bool vs) s';
//         prop_for_all__prop_of_bool vs
//     end
//   end
