(* Inductive proofs on transition systems *)
module Pipit.System.Ind

open Pipit.System.Base

module List = FStar.List.Tot

(*** Semantics of transition system checks ***)

(* An execution step of system *)
let rec system_step_result
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (inputs: list (input & option_type_sem oracle) { Cons? inputs })
  : step_result state result =
  match inputs with
  | [i, o] -> t.step i o t.init
  | (i, o) :: inputs' ->
    let pre = system_step_result t inputs' in
    let stp = t.step i o pre.s in
    stp

(* Check whether preconditions hold now and in past *)
let rec system_assumptions_sofar
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (inputs: list (input & option_type_sem oracle))
  : prop =
  match inputs with
  | []  -> True
  | (i, o) :: inputs' ->
    let pre = system_assumptions_sofar t inputs' in
    let stp = system_step_result t inputs in
    pre /\ option_prop_sem stp.chck.assumptions

(* Check whether postconditions hold at specific point in time *)
let system_holds
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  (inputs: list (input & option_type_sem oracle))
  : prop =
  match inputs with
  | [] -> True
  | (i, o) :: inputs' ->
    let stp = system_step_result t inputs  in
    system_assumptions_sofar t inputs ==> option_prop_sem stp.chck.obligations

(* Check whether system always holds *)
let system_holds_all
  (#input #result: Type)
  (#oracle #state: option Type)
  (t: system input oracle state result)
  : prop =
  forall (inputs: list (input & option_type_sem oracle)).
    system_holds t inputs



(*** Standard induction (1-induction) ***)

let base_case (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value): prop =
  forall (i: input) (o: option_type_sem oracle).
    let stp = t.step i o t.init in
    option_prop_sem stp.chck.assumptions ==>
    option_prop_sem stp.chck.obligations

let step_case (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value): prop =
  forall (i0 i1: input) (o0 o1: option_type_sem oracle) (s0: option_type_sem state).
    let stp1 = t.step i0 o0 s0 in
    let stp2 = t.step i1 o1 stp1.s in
    option_prop_sem stp1.chck.assumptions ==>
    option_prop_sem stp1.chck.obligations ==>
    option_prop_sem stp2.chck.assumptions ==>
    option_prop_sem stp2.chck.obligations

let induct1 (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value)
  : prop =
    base_case t /\ step_case t

let rec induct1_sound (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value)
  (inputs: list (input & option_type_sem oracle))
  : Lemma
    (requires (induct1 t))
    (ensures  (system_holds t inputs)) =
  match inputs with
  | [] -> ()
  | (i, o)::inputs' ->
    induct1_sound t inputs'

let induct1_sound_all (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value)
  : Lemma
    (requires (induct1 t))
    (ensures  (system_holds_all t)) =
  introduce forall (inputs: list (input & option_type_sem oracle)). system_holds t inputs
  with induct1_sound t inputs

(*** K-induction ***)

let rec base_case_k' (k: nat) (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value) (s: option_type_sem state) (check: prop -> prop): prop =
  match k with
  | 0 -> check True
  | _ ->
    forall (i: input) (o: option_type_sem oracle).
      let stp = t.step i o s in
      base_case_k' (k - 1) t stp.s
        (fun p ->
          check (option_prop_sem stp.chck.assumptions ==>
            (option_prop_sem stp.chck.obligations /\ p)))

let base_case_k (k: nat) (#input #value: Type) (#oracle #state: option Type) (t: system input oracle state value): prop =
  base_case_k' k t t.init (fun r -> r)

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

let induct_k (k: nat) (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value): prop =
    base_case_k k t /\ step_case_k k t


let rec induct2_sound (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value)
  (inputs: list (input & option_type_sem oracle))
  : Lemma
    (requires (induct_k 2 t))
    (ensures  (system_holds t inputs)) =
  admit ()
  (* TODO:ADMIT:update to latest F* 20251116 *)
  // match inputs with
  // | [] -> ()
  // | [i, o] -> ()
  // | [i, o; i', o'] ->
  //   normalize_term_spec (base_case_k 2 t);
  //   ()
  // | io2 :: io1 :: io0 :: inputs' ->
  //   induct2_sound t (io1 :: io0 :: inputs');
  //   induct2_sound t (io0 :: inputs');
  //   induct2_sound t (inputs');
  //   let stp0 = system_step_result t (io0 :: inputs') in
  //   let stp1 = system_step_result t (io1 :: io0 :: inputs') in
  //   let stp2 = system_step_result t (io2 :: io1 :: io0 :: inputs') in
  //   introduce system_assumptions_sofar t inputs ==> option_prop_sem stp2.chck.obligations
  //   with pf. (
  //     assert (step_case_k' 2 t stp0.s stp0.chck);
  //     normalize_term_spec (step_case_k' 2 t stp0.s stp0.chck);
  //     ()
  //   );
  //   ()

let induct2_sound_all (#input #value: Type) (#oracle #state: option Type)
  (t: system input oracle state value)
  : Lemma
    (requires (induct_k 2 t))
    (ensures  (system_holds_all t)) =
  introduce forall (inputs: list (input & option_type_sem oracle)). system_holds t inputs
  with induct2_sound t inputs

(* TODO: still require proof of general k-induction *)
