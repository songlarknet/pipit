(* Transition systems *)
module Pipit.System.Base

module PM = Pipit.Prop.Metadata

noeq
type checks (state: Type) = {
  assumptions: state -> prop;
  obligations: state -> prop;
}


(* Step functions are relations so that we can express contracts, which are underspecified.
   The recursive dependency for recursive binders XMu is easier to express as a
   relation too. The result type is `prop`, rather than a computational boolean,
   because composing the relations requires existential quantifiers. *)
noeq
type system (input: Type) (state: Type) (result: Type) = {
  init: state -> prop;

  step:
    (* Values of input variables *)
    i: input ->
    (* Starting state *)
    s: state ->
    (* New state *)
    s': state ->
    (* Return value *)
    r: result ->
    prop;

  (* Properties to check *)
  chck: checks state;
}

let map_checks (#state #state': Type) (f: state' -> state) (chck: checks state): checks state' = {
  assumptions = (fun s -> chck.assumptions (f s));
  obligations = (fun s -> chck.obligations (f s));
}

let checks_none (state: Type): checks state = {
  assumptions = (fun s -> True);
  obligations = (fun s -> True);
}

let checks_assumption (#state: Type) (f: state -> prop): checks state = {
  assumptions = (fun s -> f s);
  obligations = (fun s -> True);
}

let checks_obligation (#state: Type) (f: state -> prop): checks state = {
  assumptions = (fun s -> True);
  obligations = (fun s -> f s);
}

let checks_of_prop (#state: Type) (status: PM.prop_status) (f: state -> prop): checks state =
  match status with
  | PM.PSValid   -> checks_assumption f
  | PM.PSUnknown -> checks_obligation f

let checks_join (#state: Type) (c1 c2: checks state): checks state = {
  assumptions = (fun s -> c1.assumptions s /\ c2.assumptions s);
  obligations = (fun s -> c1.obligations s /\ c2.obligations s);
}

let rec system_steps
  (#input #state #result: Type)
  (t: system input state result)
  (inputs: list (input & state & result))
  (s': state): prop =
  match inputs with
  | [] -> t.init s'
  | ((i, s, r) :: inputs') ->
    system_steps t inputs' s /\
    t.step i s s' r


let rec system_stepn
  (#input #state #result: Type)
  (t: system input state result)
  (inputs: list (input & result))
  (s': state): prop =
  match inputs with
  | [] -> t.init s'
  | ((row, r) :: inputs') ->
    exists (s0: state).
    system_stepn t inputs' s0 /\
    t.step row s0 s' r

let system_const (#input #result: Type) (v: result): system input unit result =
  { init = (fun s -> True);
    step = (fun i s s' r -> r == v);
    chck = checks_none unit;
  }

let system_check (#input #state: Type)
  (name: string)
  (status: PM.prop_status)
  (t1: system input state bool):
       system input (bool & state) bool =
  { init = (fun s -> fst s == true /\ t1.init (snd s));
    step = (fun i s s' r ->
        t1.step i (snd s) (snd s') r /\
        // TODO: the property result (fst s') should be anded with (fst s) so it means *always* prop
        fst s' = r);
    chck =
      (checks_of_prop status (fun s -> fst s == true))
      `checks_join`
      (map_checks snd t1.chck);
  }

let system_contract_instance (#input #state1 #state2: Type)
  (status: PM.prop_status)
  (tr: system input state1 bool)
  (tg: system ('a & input) state2 bool):
       system input ((bool & bool) & (state1 & state2)) 'a =
  { init = (fun s -> fst (fst s) == true /\ snd (fst s) == true /\ tr.init (fst (snd s)) /\ tg.init (snd (snd s)));
    step = (fun i s s' r ->
        // TODO: the property results (fst (fst s')) and (snd (fst s')) should be anded with their corresponding values in s, so
        // that the property means *always* prop.
        // However, this requires some existentials, and I'm not totally convinced it's necessary since (fst (fst s')) is always an obligation
        tr.step i      (fst (snd s)) (fst (snd s')) (fst (fst s')) /\
        tg.step (r, i) (snd (snd s)) (snd (snd s')) (snd (fst s')));
    chck =
      checks_of_prop status (fun s -> fst (fst s) == true)
      `checks_join`
      checks_of_prop PM.PSValid (fun s -> fst (fst s) == true ==> snd (fst s) == true)
      `checks_join`
      (map_checks (fun s -> fst (snd s)) tr.chck)
      `checks_join`
      (map_checks (fun s -> snd (snd s)) tg.chck);
  }

let system_contract_definition (#input #state1 #state2 #state3: Type)
  (tr: system input state1 bool)
  (tg: system ('a & input) state2 bool)
  (ti: system input state3 'a):
       system input ((bool & bool) & (state1 & (state2 & state3))) 'a =
  { init = (fun s -> fst (fst s) == true /\ snd (fst s) == true /\ tr.init (fst (snd s)) /\ tg.init (fst (snd (snd s))) /\ ti.init (snd (snd (snd s))));
    step = (fun i s s' r ->
        // TODO: the property results (fst (fst s')) and (snd (fst s')) should be anded with their corresponding values in s, so
        // that the property means *always* prop.
        // However, this requires some existentials, and I'm not totally convinced it's necessary since (fst (fst s')) is always an obligation
        tr.step i      (fst (snd s)) (fst (snd s')) (fst (fst s')) /\
        tg.step (r, i) (fst (snd (snd s))) (fst (snd (snd s'))) (snd (fst s')) /\
        ti.step i      (snd (snd (snd s))) (snd (snd (snd s'))) r
        );
    chck =
      { assumptions = (fun s -> fst (fst s) == true);
        obligations = (fun s -> snd (fst s) == true) }
      `checks_join`
      (map_checks (fun s -> fst (snd s)) tr.chck)
      `checks_join`
      (map_checks (fun s -> fst (snd (snd s))) tg.chck)
      `checks_join`
      (map_checks (fun s -> snd (snd (snd s))) ti.chck);
  }

let system_project (#input #result: Type) (f: input -> result):
       system input unit result =
  { init = (fun _ -> True);
    step = (fun i s s' r -> r == f i);
    chck = checks_none unit;
  }

let system_with_input (#input #input' #state #result: Type) (f: input' -> input)
    (t: system input state result):
        system input' state result =
  { init = t.init;
    step = (fun i s s' r -> t.step (f i) s s' r);
    chck = t.chck;
  }

let system_pre (#input #state1 #v: Type) (init: v)
  (t1: system input state1 v):
       system input (state1 & v) v =
  { init = (fun s -> t1.init (fst s) /\ snd s == init);
    step = (fun i s s' r ->
      t1.step i (fst s) (fst s') (snd s') /\ r == snd s);
    chck = map_checks fst t1.chck;
  }

let system_mu (#input #input' #state1 #v: Type)
  (extend: input -> v -> input')
  (t1: system input' state1 v):
       system input state1 v =
  { init = t1.init;
    step = (fun i s s' r -> t1.step (extend i r) s s' r);
    chck = t1.chck;
  }

let system_let (#input #input' #state1 #state2 #v1 #v2: Type)
  (extend: input -> v1 -> input')
  (t1: system input  state1 v1)
  (t2: system input' state2 v2):
       system input (state1 & state2) v2 =
  { init = (fun s -> t1.init (fst s) /\ t2.init (snd s));
    step = (fun i s s' r ->
      let s1 = fst s in
      let s1' = fst s' in
      let s2 = snd s in
      let s2' = snd s' in
      exists (r1: v1).
        t1.step i s1 s1' r1 /\
        t2.step (extend i r1) s2 s2' r);
    chck = (map_checks fst t1.chck) `checks_join` (map_checks snd t2.chck);
  }

(***** Unnecessary combinators? *)

let system_ap2 (#input #state1 #state2 #value1 #value2: Type)
  (t1: system input state1 (value1 -> value2))
  (t2: system input state2 value1):
       system input (state1 & state2) value2 =
  {
    init = (fun s -> t1.init (fst s) /\ t2.init (snd s));
    step = (fun i s s' r ->
      exists (f: value1 -> value2) (a: value1).
        t1.step i (fst s) (fst s') f /\
        t2.step i (snd s) (snd s') a /\
        r == f a);
    chck =
      (map_checks fst t1.chck) `checks_join` (map_checks snd t2.chck);
  }

let system_map (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: system input state1 value1):
       system input state1 result =
  { init = t1.init;
    step = (fun i s s' r ->
      exists (r1: value1).
       t1.step i s s' r1 /\
       r == f r1);
    chck = t1.chck;
  }

let rec system_map_sem (#input #state1 #value1 #result: Type) (f: value1 -> result)
  (t1: system input state1 value1)
  (inputs: list (input & value1))
  (s': state1):
    Lemma (requires system_stepn t1 inputs s')
      (ensures system_stepn (system_map f t1) (List.Tot.map (fun (i,v) -> (i, f v)) inputs) s') =
 match inputs with
 | []  -> ()
 | (i, v) :: is' ->
   eliminate exists (s0: state1). system_stepn t1 is' s0 /\ t1.step i s0 s' v
   returns system_stepn (system_map f t1) (List.Tot.map (fun (i,v) -> (i, f v)) inputs) s'
   with hEx.
        system_map_sem f t1 is' s0
