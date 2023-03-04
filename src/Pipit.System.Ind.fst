module Pipit.System.Ind

open Pipit.System.Base

module C = Pipit.Context

let rec prop_for_all (l: list prop): prop =
 match l with
 | [] -> True
 | p :: ps -> p /\ prop_for_all ps

let base_case (#input #state: Type) (t: stepfun input state prop): prop =
  forall (i: input) (s': state) (r: prop).
    t i None s' r ==> r

let step_case (#input #state: Type) (t: stepfun input state prop): prop =
  forall (i0 i1: input) (s0: option state) (s1 s2: state) (r0 r1: prop).
    t i0 s0 s1 r0 ==> r0 ==>
    t i1 (Some s1) s2 r1 ==> r1

let induct1 (#input #state: Type)
  (t: stepfun input state prop): prop =
    base_case t /\ step_case t

let rec induct1_sound (#len: nat) (#input #state: Type)
  (t: stepfun input state prop)
  (inputs: C.vector input len)
  (props: C.vector prop len)
  (s': option state):
    Lemma
        (requires system_stepn' t inputs props s' /\ induct1 t)
        (ensures prop_for_all props) =
 match inputs, props with
 | [], [] -> ()
 | [i], [p] -> ()
 | i1 :: i0 :: is, p1 :: p0 :: ps ->
   assert (len >= 2);
   eliminate exists (s0: option state) (s1: state).
     system_stepn' #(len - 2) t is ps s0 /\
     t i0 s0 s1 p0
   returns prop_for_all props
   with h.
     induct1_sound #(len - 1) t (i0 :: is) (p0 :: ps) (Some s1)

let bmc2 (#input #state: Type) (t: stepfun input state prop): prop =
  forall (i1 i2: input) (s1 s2: state) (r1 r2: prop).
    t i1 None s1 r1 ==>
    t i2 (Some s1) s2 r2 ==>
    r2

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Causality

open Pipit.System.Exp

let exp_valid (e: exp) (vars: nat) = wf e vars /\ causal e

let exp_for_all (e: exp) (vars: nat): prop =
  forall (len: nat)
    (inputs: C.table len vars)
    (vs: C.vector value len)
    (hBS: bigstep inputs e vs).
    List.Tot.for_all (fun r -> r) vs

let prop_of_bool (b: bool): prop = b == true

let rec prop_for_all__prop_of_bool (bs: list bool):
  Lemma (requires prop_for_all (C.vector_map #(List.Tot.length bs) prop_of_bool bs))
        (ensures List.Tot.for_all (fun r -> r) bs) =
 // TODO prop_for_all__prop_of_bool easy
 admit ()

let induct1_exp (#vars: nat)
  (e: exp { exp_valid e vars }):
  Lemma (requires induct1 (system_map prop_of_bool (system_of_exp e vars)))
        (ensures exp_for_all e vars) =
  introduce forall (len: nat) (inputs: C.vector (C.row vars) len) (vs: C.vector bool len) (hBS: bigstep (C.Table inputs) e vs). List.Tot.for_all (fun r -> r) vs
  with
  begin
    system_eval_complete' e (C.Table inputs) vs hBS;
    eliminate exists (s': option (state_of_exp e)). system_stepn' (system_of_exp e vars) inputs vs s'
    returns _
    with hEx.
    begin
        system_map_sem prop_of_bool (system_of_exp e vars) inputs vs s';
        induct1_sound (system_map prop_of_bool (system_of_exp e vars)) inputs (C.vector_map prop_of_bool vs) s';
        prop_for_all__prop_of_bool vs
    end
  end
