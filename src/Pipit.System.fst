(* Transition systems *)
module Pipit.System

open Pipit.Exp.Base
open Pipit.Exp.Bigstep
open Pipit.Exp.Causality

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

(* A system we get from translating an expression *)
let xsystem (input: nat) (state: Type) = stepfun (C.vector value input) state value

let rec system_of_exp (e: exp) (vars: nat) (#hwf: squash (wf e vars)):
    state: Type & xsystem vars state =
  match e with
  | XVal v ->
    (| unit, (fun i s s' r -> r == v) |)
  | XVar x ->
    (| unit, (fun i s s' r -> r == C.vector_index i x) |)
  | XPrim2 p e1 e2 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    (| st1 * st2, (fun i s (s1', s2') r ->
       let s1, s2 = match s with
         | None -> None, None
         | Some (s1, s2) -> Some s1, Some s2
       in
       exists (r1 r2: value).
             t1 i s1 s1' r1 /\
             t2 i s2 s2' r2 /\
             r == eval_prim2 p r1 r2)
    |)
  | XPre e1 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    (| st1 * value, (fun i s (s1', v') r ->
      let s1, v = match s with
        | None -> None, xpre_init
        | Some (s1, v) -> Some s1, v
      in
      t1 i s1 s1' v' /\ r == v) |)
  | XThen e1 e2 ->
    let (| st1, t1 |) = system_of_exp e1 vars in
    let (| st2, t2 |) = system_of_exp e2 vars in
    (| st2, (fun i s s' r ->
       match s with
       | None -> exists s1' r'. t1 i None s1' r /\ t2 i None s' r'
       | Some _ -> t2 i s s' r)
    |)
  | XMu e1 ->
    let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
    (| st1, (fun (i: C.vector value vars) s s' r ->
      t1 (r :: i) s s' r) |)
  
let rec step0_ok
  (#vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (#hwf: squash (wf e vars))
  (#hsys: squash (system_of_exp e vars == (| state, t|)))
  (row: C.vector value vars)
  (r r': value)
  (s': state)
  (hBS: bigstep (C.table1 (C.Row row)) e (C.vector1 r))
  (#ht: squash (t row None s' r')):
   Tot (squash (r == r')) (decreases e) =
 match e with
 | XVal _ -> ()
 | XVar _ -> ()
 | XPrim2 p e1 e2 ->
   let BSPrim2 _ _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
   let (| st1, t1 |) = system_of_exp e1 vars in
   let (| st2, t2 |) = system_of_exp e2 vars in
   let (s1', s2') = s' <: (st1 * st2) in
   eliminate exists (r1' r2': value). t1 row None s1' r1' /\ t2 row None s2' r2' /\ r' == eval_prim2 p r1' r2'
   returns r == r'
   with hEx. begin
     let _ = step0_ok e1 t1 row r1 r1' s1' hBS1 in
     let _ = step0_ok e2 t2 row r2 r2' s2' hBS2 in
     ()
   end
 | XPre e1 -> ()
 | XThen e1 e2 ->
   let BSThen _ _ _ [r1] [r2] hBS1 hBS2 = hBS in
   let (| st1, t1 |) = system_of_exp e1 vars in
   let (| st2, t2 |) = system_of_exp e2 vars in
   eliminate exists (s1': st1) (r2': value). t1 row None s1' r' /\ t2 row None s' r2'
   returns r == r'
   with hEx. begin
     let _ = step0_ok e1 t1 row r1 r' s1' hBS1 in
     ()
   end
 | XMu e1 ->
   let BSMu _ _ [r] hBS1 = hBS in
   let (| st1, t1 |) = system_of_exp e1 (vars + 1) in
   let hBS' = bigstep_recursive_XMu #0 e1 (C.table1 (C.Row row)) [] r r' hBS in
   let _ = step0_ok e1 t1 (r' :: row) r r' s' hBS' in
   ()
