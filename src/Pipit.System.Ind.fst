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

let base_case (#input #state #value: Type) (t: system input state value): prop =
  forall (i: input) (s: state) (s': state) (r: value).
    t.init s ==> t.step i s s' r ==>
    all_checks_hold t s'

let step_case (#input #state #value: Type) (t: system input state value): prop =
  forall (i0 i1: input) (s0: state) (s1 s2: state) (r0 r1: value).
    t.step i0 s0 s1 r0 ==> all_checks_hold t s1 ==>
    t.step i1 s1 s2 r1 ==> all_checks_hold t s2

// WRONG quantifiers in the wrong place
let rec step_case_k' (k: nat) (#input #state #value: Type) (t: system input state value) (s': state): prop =
  match k with
  | 0 ->
    forall (i: input) (s: state) (r: value).
        t.step i s s' r ==>
        all_checks_hold t s'
  | _ ->
  forall (i: input) (s: state) (r: value).
    step_case_k' (k - 1) t s ==>
    t.step i s s' r ==>
    all_checks_hold t s'

// let rec step_case_k' (k: nat) (#input #state #value: Type) (t: system input state value) (s': state): prop =
//   forall (i: input) (s: state) (r: value).
//     let step' =
//       if k = 0
//       then True
//       else step_case_k' (k - 1) t s
//     in
//     step' ==>
//     t.step i s s' r ==>
//     all_checks_hold t s'

let step_case_k (k: nat) (#input #state #value: Type) (t: system input state value): prop =
  forall (s': state). step_case_k' k t s'

// let chk (t: system 'i 's 'v): unit =
//   assert (step_case t == step_case_k 1 t) by (FStar.Tactics.norm [nbe; delta; zeta; iota; primops]; FStar.Tactics.norm [delta_fully ["Pipit.System.Ind.step_case_k"; "Pipit.System.Ind.step_case_k'"]]; FStar.Tactics.dump "ok")

let step_case_2 (#input #state #value: Type) (t: system input state value): prop =
  forall (i0 i1 i2: input) (s0 s1 s2 s3: state) (r0 r1 r2: value).
    t.step i0 s0 s1 r0 ==> all_checks_hold t s1 ==>
    t.step i1 s1 s2 r1 ==> all_checks_hold t s2 ==>
    t.step i2 s2 s3 r2 ==> all_checks_hold t s3

let step_case_3 (#input #state #value: Type) (t: system input state value): prop =
  forall (i0 i1 i2 i3: input) (s0 s1 s2 s3 s4: state) (r0 r1 r2 r3: value).
    t.step i0 s0 s1 r0 ==> all_checks_hold t s1 ==>
    t.step i1 s1 s2 r1 ==> all_checks_hold t s2 ==>
    t.step i2 s2 s3 r2 ==> all_checks_hold t s3 ==>
    t.step i3 s3 s4 r3 ==> all_checks_hold t s4

let step_case_4 (#input #state #value: Type) (t: system input state value): prop =
  forall (i0 i1 i2 i3 i4: input) (s0: state) (s1 s2 s3 s4 s5: state) (r0 r1 r2 r3 r4: value).
    t.step i0 s0 s1 r0 ==> all_checks_hold t s1 ==>
    t.step i1 s1 s2 r1 ==> all_checks_hold t s2 ==>
    t.step i2 s2 s3 r2 ==> all_checks_hold t s3 ==>
    t.step i3 s3 s4 r3 ==> all_checks_hold t s4 ==>
    t.step i4 s4 s5 r4 ==> all_checks_hold t s5

let induct1 (#input #state #value: Type)
  (t: system input state value): prop =
    base_case t /\ step_case t

// let rec induct1_sound (#len: nat) (#input #state: Type)
//   (t: system input state prop)
//   (inputs: C.vector input len)
//   (props: C.vector prop len)
//   (s': state):
//     Lemma
//         (requires system_stepn t inputs props s' /\ induct1 t)
//         (ensures prop_for_all props) =
//  match inputs, props with
//  | [], [] -> ()
//  | [i], [p] -> ()
//  | i1 :: i0 :: is, p1 :: p0 :: ps ->
//    assert (len >= 2);
//    eliminate exists (s0: state) (s1: state).
//      system_stepn #(len - 2) t is ps s0 /\
//      t.step i0 s0 s1 p0
//    returns prop_for_all props
//    with h.
//      induct1_sound #(len - 1) t (i0 :: is) (p0 :: ps) s1

// let bmc2' (#input #state: Type) (t: system input state C.value): prop =
//   forall (i1 i2: input) (s0 s1 s2: state) (r1 r2: C.value).
//     t.init s0 ==>
//     t.step i1 s0 s1 r1 ==>
//     t.step i2 s1 s2 r2 ==>
//     r2 <> 0

// let bmc2 (#input #state: Type) (t: system input state prop): prop =
//   forall (i1 i2: input) (s0 s1 s2: state) (r1 r2: prop).
//     t.init s0 ==>
//     t.step i1 s0 s1 r1 ==>
//     t.step i2 s1 s2 r2 ==>
//     r2

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
//  // TODO prop_for_all__prop_of_bool easy
//  admit ()

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
