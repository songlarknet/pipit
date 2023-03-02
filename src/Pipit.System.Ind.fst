module Pipit.System.Ind

open Pipit.System.Base

module C = Pipit.Context

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

let rec prop_for_all (l: list prop): prop =
 match l with
 | [] -> True
 | p :: ps -> p /\ prop_for_all ps

let rec induct1_sound (#len: nat { len > 0 }) (#input #state: Type)
  (t: stepfun input state prop)
  (inputs: C.vector input len)
  (props: C.vector prop len)
  (s': option state):
    Lemma
        (requires system_stepn' t inputs props s' /\ induct1 t)
        (ensures prop_for_all props) =
 match inputs, props with
 | [i], [p] ->
   ()
 | i1 :: i0 :: is, p1 :: p0 :: ps ->
   assert (len >= 2);
   eliminate exists (s0: option state) (s1: state).
     system_stepn' #(len - 2) t is ps s0 /\
     t i0 s0 s1 p0
   returns prop_for_all props
   with h.
     induct1_sound #(len - 1) t (i0 :: is) (p0 :: ps) (Some s1)
