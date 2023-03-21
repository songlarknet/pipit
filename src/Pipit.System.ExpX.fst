(* Improved translation to transition system *)
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
  | XIte ep e1 e2 -> state_of_exp ep * state_of_exp e1 * state_of_exp e2
  | XPre e1 -> state_of_exp e1 * value
  | XThen e1 e2 -> bool * state_of_exp e2
  | XMu e1 -> state_of_exp e1
  | XLet e1 e2 -> state_of_exp e1 * state_of_exp e2

let rec values_n (n: nat): Type =
  match n with
  | 0 -> unit
  | n -> value * values_n (n - 1)

let rec values_index (n: nat) (index: nat { index < n }) (values: values_n n): value =
  match index, (values <: (value * values_n (n - 1))) with
  | 0, (v, rest) -> v
  | index, (v, rest) -> values_index (n - 1) (index - 1) rest

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

type ite_oracle (valuep value1 value2 oraclep oracle1 oracle2: Type) = {
     ite_rp: valuep;
     ite_r1: value1;
     ite_r2: value2;
     ite_op: oraclep;
     ite_o1: oracle1;
     ite_o2: oracle2;
  }


let rec oracle_of_exp (e: exp): Type =
  match e with
  | XVal v -> unit
  | XVar x -> unit
  | XPrim2 p e1 e2 -> map2_oracle value value (oracle_of_exp e1) (oracle_of_exp e2)
  | XIte ep e1 e2 -> ite_oracle value value value (oracle_of_exp ep) (oracle_of_exp e1) (oracle_of_exp e2)
  | XPre e1 -> oracle_of_exp e1
  | XThen e1 e2 -> then_oracle (state_of_exp e1) value (oracle_of_exp e1) (oracle_of_exp e2)
  | XMu e1 -> oracle_of_exp e1
  | XLet e1 e2 -> value * (oracle_of_exp e1 * oracle_of_exp e2)

(* An system with "oracles", which let us draw out the quantifiers to the top level *)
let osystem (input: Type) (oracle: Type) (state: Type) (result: Type) = system (input * oracle) state result

(* A system we get from translating an expression *)
let xsystem (e: exp) (vars: nat { wf e vars }) = osystem (values_n vars) (oracle_of_exp e) (state_of_exp e) value

let osystem_input (#input #oracle: Type): osystem input oracle unit input =
  { init = (fun s -> True);
    step = (fun io s s' r -> r == (fst io)) }

let osystem_index (vars: nat) (x: nat { x < vars }):
       osystem (values_n vars) unit unit value =
  { init = (fun _ -> True);
    step = (fun io s s' r ->
      r == values_index vars x (fst io))
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

let osystem_ite (#input #oraclep #oracle1 #oracle2 #statep #state1 #state2 #valuep #value: Type) (f: valuep -> bool)
  (tp: osystem input oraclep statep valuep)
  (t1: osystem input oracle1 state1 value)
  (t2: osystem input oracle2 state2 value):
       osystem input (ite_oracle valuep value value oraclep oracle1 oracle2) (statep * state1 * state2) value =
   {
    init = (fun (sp, s1, s2) -> tp.init sp /\ t1.init s1 /\ t2.init s2);
    step = (fun (i, o) (sp, s1, s2) (sp', s1', s2') r ->
               tp.step (i, o.ite_op) sp sp' o.ite_rp /\
               t1.step (i, o.ite_o1) s1 s1' o.ite_r1 /\
               t2.step (i, o.ite_o2) s2 s2' o.ite_r2 /\
               r == (if f o.ite_rp then o.ite_r1 else o.ite_r2))
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
     not (fst s') /\ t2.step (i, o.then_o2) (snd s) (snd s') o.then_r2 /\
      (if fst s
      then t1.init o.then_s1 /\ t1.step (i, o.then_o1) o.then_s1 o.then_s1' r
      else r == o.then_r2))
  }

let osystem_mu (#input #input' #oracle #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: osystem input' oracle state1 v):
       osystem input  oracle state1 v =
  { init = t1.init;
    step = (fun io s s' r -> t1.step (extend (fst io) r, snd io) s s' r)
  }

let osystem_let (#input #input' #oracle1 #oracle2 #state1 #state2 #v1 #v2: Type)
  (extend: input -> v1 -> input')
  (t1: osystem input  oracle1 state1 v1)
  (t2: osystem input' oracle2 state2 v2):
       osystem input  (v1 * (oracle1 * oracle2)) (state1 * state2) v2 =
  { init = (fun s -> t1.init (fst s) /\ t2.init (snd s));
    step = (fun io s s' r ->
      let i = fst io in
      let o = snd io in
      let v1 = fst o in
      let o1 = fst (snd o) in
      let o2 = snd (snd o) in
      t1.step (i, o1) (fst s) (fst s') v1 /\
      t2.step (extend i v1, o2) (snd s) (snd s') r)
  }

let rec osystem_of_exp (e: exp) (vars: nat { wf e vars }):
    xsystem e vars =
  match e with
  | XVal v -> system_const v
  | XVar x -> osystem_index vars x
  | XPrim2 p e1 e2 ->
    osystem_map2 (eval_prim2 p) (osystem_of_exp e1 vars) (osystem_of_exp e2 vars)
  | XIte ep et ef ->
    osystem_ite (fun v -> v <> 0) (osystem_of_exp ep vars) (osystem_of_exp et vars) (osystem_of_exp ef vars)
  | XPre e1 ->
    osystem_pre xpre_init (osystem_of_exp e1 vars)
  | XThen e1 e2 ->
    osystem_then (osystem_of_exp e1 vars) (osystem_of_exp e2 vars)
  | XMu e1 ->
    let t = osystem_of_exp e1 (vars + 1) in
    osystem_mu #(values_n vars) #(values_n (vars + 1)) (fun i v -> (v, i)) t
  | XLet e1 e2 ->
    let t1 = osystem_of_exp e1 vars in
    let t2 = osystem_of_exp e2 (vars + 1) in
    osystem_let #(values_n vars) #(values_n (vars + 1)) (fun i v -> (v, i)) t1 t2

module T = FStar.Tactics


let tac_nbe (): T.Tac unit = T.norm [primops; iota; delta; zeta; nbe]

let rec type_is_product (ty: T.typ): T.Tac bool =
  match T.inspect_unascribe ty with
  | T.Tv_FVar fv | T.Tv_UInst fv _ ->
    let nm = T.inspect_fv fv in
    begin
      match nm with
      | ["FStar"; "Pervasives"; "Native"; tt ] ->
        tt <> "option"
      | ["Pipit"; "Context"; "Base"; "row" ]
      | ["Pipit"; "System"; "ExpX"; "ite_oracle" ]
      | ["Pipit"; "System"; "ExpX"; "then_oracle" ]
      | ["Pipit"; "System"; "ExpX"; "map2_oracle" ] ->
        true
      | _ -> false
    end
  | T.Tv_App f _ -> type_is_product f
  | T.Tv_Const T.C_Unit -> true
  | _ ->
    false

let type_is_unit (ty: T.typ): T.Tac bool =
  match T.inspect_unascribe ty with
  | T.Tv_FVar fv | T.Tv_UInst fv _ ->
    let nm = T.inspect_fv fv in
    begin
      match nm with
      | ["Prims"; "unit"] ->
        true
      | _ -> false
    end
  | _ ->
    false

let rec tac_products (bs: list T.binder): T.Tac unit = match bs with
 | [] -> ()
 | b :: bs ->
   let open T in
   let open FStar.List.Tot in
   let tm = T.binder_to_term b in
   let ty = T.type_of_binder b in
   if type_is_product ty
   then begin
    T.destruct tm;
    let bs' = T.repeat T.intro in
    T.rewrite_all_context_equalities bs';
    T.norm [iota];
    let _ = T.trytac (fun () ->
      match List.Tot.rev bs' with
      | breq :: _ -> clear breq; clear b
      | _ -> clear b
    ) in
    tac_products (bs' @ bs)
   end
   else begin
    (try
      if type_is_unit ty then clear b
    with
      | _ -> ());
    tac_products bs
    end

let tac_products_all (): T.Tac unit =
  let bs = T.cur_binders () in
  tac_products bs

(* Tactic for proving base case *)
let tac_base (): T.Tac unit =
  // Compute to simplify state_of_exp and osystem_of_exp as much as possible
  tac_nbe ();
  // Introduce the input, state and result quantifiers
  let i  = T.forall_intro () in
  let s  = T.forall_intro () in
  let s' = T.forall_intro () in
  let r = T.forall_intro () in
  // Tease apart the nested tuples in the states etc
  tac_products [i; s; s'; r];
  // Pulling apart the states might expose a little more reduction, so take it
  tac_nbe ()

(* Tactic for proving step case *)
let tac_step (): T.Tac unit =
  tac_nbe ();
  let i0  = T.forall_intro () in
  let i1  = T.forall_intro () in
  let s0 = T.forall_intro () in
  let s1 = T.forall_intro () in
  let s2 = T.forall_intro () in
  let r0 = T.forall_intro () in
  let r1 = T.forall_intro () in
  // Tease apart the nested tuples in the states etc
  tac_products [i0; i1; s0; s1; s2; r0; r1];
  // Pulling apart the states might expose a little more reduction, so take it
  tac_nbe ()

