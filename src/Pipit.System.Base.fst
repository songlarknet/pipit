(* Transition systems *)
module Pipit.System.Base

module C = Pipit.Context

(* Step functions are relations so that we can express non-deterministic systems.
   The recursive dependency for recursive binders XMu is easier to express as a
   relation too. The result type is `prop`, rather than a computational boolean,
   because composing the relations requires existential quantifiers. *)
type stepfun (input: Type) (state: Type) (result: Type) =
  (* Values of input variables *)
  i: input ->
  (* Starting state, or None for initial *)
  s: option state ->
  (* New state *)
  s': state ->
  (* Return value *)
  r: result ->
  prop

let rec system_stepn'
  (#outer: nat)
  (#input #state #result: Type)
  (t: stepfun input state result)
  (inputs: C.vector input outer)
  (vs: C.vector result outer)
  (s': option state): prop =
  match inputs, vs with
  | [], [] -> s' == None
  | (row :: inputs'), r :: vs' ->
    match s' with
    | Some s' ->
        exists (s0: option state).
        system_stepn' #(outer - 1) t inputs' vs' s0 /\
        t row s0 s' r
    | None -> False

let system_stepn
  (#outer: nat)
  (#input #state #result: Type)
  (t: stepfun input state result)
  (inputs: C.vector input (outer + 1))
  (vs: C.vector result (outer + 1))
  (s': state): prop =
  system_stepn' t inputs vs (Some s')

let system_map (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: stepfun input state1 value1):
       stepfun input state1 result =
  (fun i s s' r ->
     let s1  = s in
     let s1' = s' in
     exists (r1: value1).
               t1 i s1 s1' r1 /\
               r == f r1)

let system_map2 (#input #state1 #state2 #value1 #value2 #result: Type) (f: value1 -> value2 -> result)
  (t1: stepfun input state1 value1)
  (t2: stepfun input state2 value2):
       stepfun input (state1 * state2) result =
  (fun i s s' r ->
     let s1, s2 = match s with
         | None -> None, None
         | Some (s1, s2) -> Some s1, Some s2
     in
     let s1', s2' = s' in
     exists (r1: value1) (r2: value2).
               t1 i s1 s1' r1 /\
               t2 i s2 s2' r2 /\
               r == f r1 r2)

let system_pre (#input #state1 #v: Type) (init: v)
  (t1: stepfun input state1 v):
       stepfun input (state1 * v) v =
  (fun i s s' r ->
      let s1, v = match s with
      | None -> None, init
      | Some (s1, v) -> Some s1, v
      in
      let s1', v' = s' in
      t1 i s1 s1' v' /\ r == v)

let system_then (#input #state1 #state2 #v: Type)
  (t1: stepfun input state1 v)
  (t2: stepfun input state2 v):
       stepfun input state2 v =
  (fun i s s' r ->
     match s with
     | None -> exists s1' r'. t1 i None s1' r /\ t2 i None s' r'
     | Some _ -> t2 i s s' r)

let system_mu (#input #input' #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: stepfun input' state1 v):
       stepfun input state1 v =
  (fun i s s' r ->
      t1 (extend i r) s s' r)
