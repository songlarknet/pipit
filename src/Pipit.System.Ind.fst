(* Inductive proofs on transition systems *)
module Pipit.System.Ind

open Pipit.System.Base

let rec prop_for_all (l: list prop): prop =
 match l with
 | [] -> True
 | p :: ps -> p /\ prop_for_all ps

// let system_holds (#input #state #value: Type) (t: system input state value): prop =
//   forall (inputs: list (input & value)) (s: state).
//     Cons? inputs            ==>
//     system_stepn t inputs s ==>
//     t.chck.assumptions s ==>
//     t.chck.obligations s

let base_case (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value): prop =
  forall (i: input) (o: option_type_sem oracle).
    let stp = t.step i o t.init in
    option_prop_sem stp.chck.assumptions ==>
    option_prop_sem stp.chck.obligations

// TODO: change base case for k to split out to separate checks for each length, eg
// base_case_k 3 =
//   (forall s0. t.init s0 ==> t.chck.assumptions s0 ==> t.chck.obligations s0) /\
//   (forall s0 s1. t.init s0 ==> t.step s0 s1 ==> t.chck.assumptions s0 ==> t.chck.assumptions s1 ==> t.chck.obligations s1) /\
//   (forall s0 s1 s2. t.init s0 ==> t.step s0 s1 ==> t.step s1 s2 ==> t.chck.assumptions s0 ==> t.chck.assumptions s1 ==> t.chck.assumptions s2 ==> t.chck.obligations s2)
// this makes the proof obligation larger, but should make the soundness proof easier as we won't be assuming that step is always defined (which it isn't for contracts with questionable assumptions)
// would it make sense to spell out step requirements explicitly? eg,
//   forall s0. t.chck.assumptions s0 ==> exists s1. t.step s0 s1
// but this quantifier alternation looks like it would be difficult to solve automatically
let rec base_case_k' (k: nat) (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value) (s: option_type_sem state) (check: prop): prop =
  match k with
  | 0 -> check
  | _ ->
    forall (i: input) (o: option_type_sem oracle).
      let stp = t.step i o s in
      base_case_k' (k - 1) t stp.s
        (option_prop_sem stp.chck.assumptions ==>
        (option_prop_sem stp.chck.obligations /\ check))

let base_case_k (k: nat) (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value): prop =
  base_case_k' k t t.init True

let step_case (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value): prop =
  forall (i0 i1: input) (o0 o1: option_type_sem oracle) (s0: option_type_sem state).
    let stp1 = t.step i0 o0 s0 in
    let stp2 = t.step i1 o1 stp1.s in
    option_prop_sem stp1.chck.assumptions ==>
    option_prop_sem stp1.chck.obligations ==>
    option_prop_sem stp2.chck.assumptions ==>
    option_prop_sem stp2.chck.obligations

let rec step_case_k' (k: nat) (#input #value: Type) (#oracle #state: option Type)  (t: system input oracle state value) (s: option_type_sem state) (chck: checks): prop =
  match k with
  | 0 -> option_prop_sem chck.assumptions ==> option_prop_sem chck.obligations
  | _ -> forall (i: input) (o: option_type_sem oracle).
    let stp = t.step i o s in
    option_prop_sem chck.assumptions ==>
    option_prop_sem chck.obligations ==>
    step_case_k' (k - 1) t stp.s stp.chck

let step_case_k (k: nat) (#input #value: Type) (#oracle #state: option Type)  (t: system input oracle state value): prop =
  forall (i: input) (o: option_type_sem oracle) (s: option_type_sem state).
    let stp = t.step i o s in
    step_case_k' k t stp.s stp.chck

let induct1 (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value): prop =
    base_case t /\ step_case t

// let rec induct1_sound' (#input #state #value: Type)
//   (t: system input state value)
//   (inputs: list (input & value))
//   (s': state):
//     Lemma
//         (requires system_stepn t inputs s' /\ induct1 t /\ Cons? inputs)
//         (ensures all_checks_hold t s')
//         (decreases inputs) =
//   match inputs with
//   | [] -> ()
//   | [(i, v)] -> ()
//   | (i1,v1) :: (i0,v0) :: ivs ->
//     eliminate exists (s0: state) (s1: state).
//       system_stepn t ivs s0 /\
//       t.step i0 s0 s1 v0 /\
//       t.step i1 s1 s' v1
//     returns all_checks_hold t s'
//     with h.
//       (induct1_sound' t ((i0, v0) :: ivs) s1)

// let induct1_sound (#input #state #value: Type)
//   (t: system input state value):
//     Lemma
//         (requires induct1 t)
//         (ensures system_holds t) =
//   introduce forall (inputs: list (input & value) { Cons? inputs }) (s: state { system_stepn t inputs s }).
//     (Cons? inputs) ==>
//     system_stepn t inputs s ==>
//     all_checks_hold t s
//   with
//     (induct1_sound' t inputs s)

let induct_k (k: nat) (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value): prop =
    base_case_k k t /\ step_case_k k t

(* The current formulation of the base case makes it difficult to prove
   that k-induction is sound. The issue is that base_case_k 2 has the shape:
   >  forall s0 s1 s2.
   >    t.init s0 /\
   >    t.step s0 s1 /\
   >    t.step s1 s2 /\
   >    all_checks_hold s1 /\
   >    all_checks_hold s2

   To prove induction is sound assuming base_case_k and step_case_k,
   you want to show that for a single step s0 to s1, the checks
   hold. But what do you instantiate s2 to in the above? This would
   be easier for deterministic systems.
   We could restate base_case_k 2 as something like:

   >  forall s0 s1.
   >    t.init s0 /\
   >    t.step s0 s1 /\
   >    all_checks_hold s1 /\
   >    forall s2.
   >      t.step s1 s2 /\
   >      all_checks_hold s2

   But proving this for user programs would require the pipit_simplify tactic to
   split apart the conjunctions, which it doesn't do right now.
*)

// let rec induct2_sound' (#input #state #value: Type)
//   (t: system input state value)
//   (inputs: list (input & value))
//   (s': state):
//     Lemma
//         (requires system_stepn t inputs s' /\ induct_k 2 t)
//         (ensures Nil? inputs \/ all_checks_hold t s')
//         (decreases inputs) =
//   match inputs with
//   | [] -> ()
//   | [(i0, v0)] -> ()
//   | [(i0, v0); (i1, v1)] -> ()
//   | (i2,v2) :: (i1,v1) :: (i0,v0) :: ivs ->
//     eliminate exists (s0: state) (s1: state) (s2: state).
//       system_stepn t ivs s0 /\
//       t.step i0 s0 s1 v0 /\
//       t.step i1 s1 s2 v1 /\
//       t.step i2 s2 s' v2
//     returns all_checks_hold t s'
//     with h.
//       (induct2_sound' t ((i1, v1) :: (i0, v0) :: ivs) s2;
//       induct2_sound' t ((i0, v0) :: ivs) s1;
//       ())

// let induct2_sound (#input #state #value: Type)
//   (t: system input state value):
//     Lemma
//         (requires induct_k 2 t)
//         (ensures system_holds t) =
//   introduce forall (inputs: list (input & value) { Cons? inputs }) (s: state { system_stepn t inputs s }).
//     (Cons? inputs) ==>
//     system_stepn t inputs s ==>
//     all_checks_hold t s
//   with
//     (induct2_sound' t inputs s)

// let induct_k_sound (k: nat) (#input #state #value: Type)
//   (t: system input state value):
//     Lemma
//         (requires induct_k k t)
//         (ensures system_holds t) =
//   introduce forall (inputs: list (input & value) { Cons? inputs }) (s: state { system_stepn t inputs s }).
//     (Cons? inputs) ==>
//     system_stepn t inputs s ==>
//     all_checks_hold t s
//   with
//     // TODO inductk_sound
//     admit ()


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
