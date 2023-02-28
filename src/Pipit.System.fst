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

(* A system we get from translating an expression *)
let xsystem (input: nat) (state: Type) = stepfun (C.vector value input) state value


let rec state_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> state_of_exp e1 * state_of_exp e2
  | XPre e1 -> state_of_exp e1 * value
  | XThen e1 e2 -> state_of_exp e2
  | XMu e1 -> state_of_exp e1

unfold
let explicit_cast (#a: Type) (b: Type { a == b }) (input: a): b = input

let rec system_of_exp (e: exp) (vars: nat { wf e vars }):
    xsystem vars (state_of_exp e) =
  match e with
  | XVal v -> (fun i s s' r -> r == v)
  | XVar x -> (fun i s s' r -> r == C.vector_index i x)
  | XPrim2 p e1 e2 ->
    system_map2 (eval_prim2 p) (system_of_exp e1 vars) (system_of_exp e2 vars)
  | XPre e1 ->
    system_pre xpre_init (system_of_exp e1 vars)
  | XThen e1 e2 ->
    let t: xsystem vars (state_of_exp e2) =
      system_then (system_of_exp e1 vars) (system_of_exp e2 vars)
    in
    explicit_cast (xsystem vars (state_of_exp e)) t
  | XMu e1 ->
    let t: xsystem (vars + 1) (state_of_exp e1) =
      system_of_exp e1 (vars + 1)
    in
    let t': xsystem vars (state_of_exp e1) =
      system_mu #(C.vector value vars) #(C.vector value (vars + 1)) (fun i v -> v :: i) t
    in
    explicit_cast (xsystem vars (state_of_exp e)) t'

let rec stepn
  (#outer #vars: nat)
  (#state: Type)
  (e: exp)
  (t: xsystem vars state)
  (streams: C.table (outer + 1) vars)
  (vs: C.vector value (outer + 1))
  (s': state): prop =
  match streams, vs with
  | C.Table [C.Row row], [r] -> t row None s' r
  | C.Table (C.Row row :: streams'), r :: vs' ->
    exists (s'': state).
      stepn #(outer - 1) e t (C.Table streams') vs' s'' /\
      t row (Some s'') s' r

let rec system_of_exp_invariant
  (#outer #vars: nat)
  (e: exp { wf e vars /\ causal e })
  (streams: C.table (outer + 1) vars)
  (vs: C.vector value (outer + 1))
  (hBS: bigstep streams e vs)
  (s: state_of_exp e):
    Tot prop (decreases e) =
  match e with
  | XVar _ -> unit
  | XVal _ -> unit
  | XPrim2 _ e1 e2 ->
    let (s1, s2) = s <: (state_of_exp e1 * state_of_exp e2) in
    let BSPrim2 _ _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
    system_of_exp_invariant e1 streams vs1 hBS1 s1 /\
    system_of_exp_invariant e2 streams vs2 hBS2 s2
  | XPre e1 ->
    let BSPre _ _ _ vs1 hBS1 = hBS in
    let v1'   = bigstep_monotone_inv_next #outer #vars #streams hBS1 in
    let hBS1' = bigstep_monotone_inv #outer #vars #streams hBS1 in
    let (s1, v1) = s <: (state_of_exp e1 * value) in
    (system_of_exp_invariant #outer #vars e1 streams (v1' :: vs1) hBS1' s1 /\ v1 == v1')

  | XThen e1 e2 ->
    let s2 = explicit_cast (state_of_exp e2) s in
    let BSThen _ _ _ vs1 vs2 hBS1 hBS2 = hBS in
    system_of_exp_invariant e2 streams vs2 hBS2 s2
  | XMu e1 ->
    let s1 = explicit_cast (state_of_exp e1) s in
    let BSMu _ _ vs1 hBS1 = hBS in
    let hBS' = bigstep_substitute_XMu e1 streams vs hBS in
    system_of_exp_invariant #outer #(vars + 1) e1 (C.table_map_append (C.table_of_values vs1) streams) vs1 hBS' s1

let rec step0_ok
  (#vars: nat)
  (e: exp { causal e /\ wf e vars })
  (row: C.vector value vars)
  (v: value)
  (hBS: bigstep (C.Table [C.Row row]) e [v]):
    Tot (s': state_of_exp e & u: unit { system_of_exp e vars row None s' v /\ system_of_exp_invariant #0 e (C.Table [C.Row row]) [v] hBS s' }) (decreases e) =
  let streams = (C.Table #1 #vars [C.Row #vars row]) in
  match e with
  | XVal _ -> (| (), () |)
  | XVar x -> (| (), () |)

  | XPrim2 p e1 e2 ->
    let BSPrim2 _ _ _ _ [v1] [v2] hBS1 hBS2 = hBS in
    let (| s1', () |) = step0_ok e1 row v1 hBS1 in
    let (| s2', () |) = step0_ok e2 row v2 hBS2 in
    (| (s1', s2'), () |)

  | XPre e1 ->
    let BSPre _ _ _ [] hBS1 = hBS in
    let v1 = bigstep_monotone_inv_next #0 #vars #streams hBS1 in
    let hBS1' = bigstep_monotone_inv #0 #vars #streams hBS1 in
    let (| s1', () |) = step0_ok e1 row v1 hBS1' in
    (| (s1', v1), () |)

  | XThen e1 e2 ->
    let BSThen _ _ _ [v1] [v2] hBS1 hBS2 = hBS in
    let (| s1', () |) = step0_ok e1 row v1 hBS1 in
    let (| s2', () |) = step0_ok e2 row v2 hBS2 in
    (| explicit_cast (state_of_exp e) s2', () |)

  | XMu e1 ->
    let hBS' = bigstep_substitute_XMu e1 streams [v] hBS in
    let (| s1', () |) = step0_ok e1 (v :: row) v hBS' in
    (| explicit_cast (state_of_exp e) s1', () |)
