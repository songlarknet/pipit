(* Transition systems *)
module Pipit.System.Base

module PM = Pipit.Prop.Metadata

noeq
type check (state: Type) =
  | Check:
    name: string ->
    status: PM.prop_status ->
    obligation: (state -> bool) ->
    check state
  | ContractInstance:
    status: PM.prop_status ->
    rely: (state -> bool) ->
    guar: (state -> bool) ->
    check state

type checks (state: Type) = list (check state)


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

let map_check (#state #state': Type) (f: state' -> state) (chck: check state): check state' =
  match chck with
  | Check n st o -> Check n st (fun s -> o (f s))
  // | Assume a -> Assume (fun s -> a (f s))
  | ContractInstance st r g -> ContractInstance st (fun s -> r (f s)) (fun s -> g (f s))

let map_checks (#state #state': Type) (f: state' -> state) (chck: checks state): checks state' =
  List.Tot.map (map_check f) chck

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
    chck = [];
  }

let system_check (#input #state: Type)
  (name: string)
  (status: PM.prop_status)
  (t1: system input state bool):
       system input (bool & state) bool =
  { init = (fun s -> fst s == true /\ t1.init (snd s));
    step = (fun i s s' r ->
        t1.step i (snd s) (snd s') r /\
        r = fst s');
    chck = Check name status (fun s -> fst s) :: map_checks snd t1.chck;
  }

let system_contract_instance (#input #state1 #state2: Type)
  (status: PM.prop_status)
  (tr: system input state1 bool)
  (tg: system ('a & input) state2 bool):
       system input ((bool & bool) & (state1 & state2)) 'a =
  { init = (fun s -> fst (fst s) == true /\ snd (fst s) == true /\ tr.init (fst (snd s)) /\ tg.init (snd (snd s)));
    step = (fun i s s' r ->
        tr.step i (fst (snd s)) (fst (snd s')) (fst (fst s)) /\
        tg.step (r, i) (snd (snd s)) (snd (snd s')) (snd (fst s)));
    chck = ContractInstance status (fun s -> fst (fst s)) (fun s -> fst (fst s)) ::
    List.Tot.append
      (map_checks (fun s -> fst (snd s)) tr.chck)
      (map_checks (fun s -> snd (snd s)) tg.chck) ;
  }

let system_project (#input #result: Type) (f: input -> result):
       system input unit result =
  { init = (fun _ -> True);
    step = (fun i s s' r -> r == f i);
    chck = [];
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
    chck = List.Tot.append (map_checks fst t1.chck) (map_checks snd t2.chck);
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
      List.Tot.append (map_checks fst t1.chck) (map_checks snd t2.chck);
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

// why is this necessary? issue with type inference for prop vs logical
let prop_holds (p: prop): prop = p

let system_bool_holds (#input #state: Type) (t: system input state bool):
  system input state prop =
  system_map (fun b -> prop_holds (b == true)) t
