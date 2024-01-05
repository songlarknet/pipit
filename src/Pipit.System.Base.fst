(* Transition systems *)
module Pipit.System.Base

module PM = Pipit.Prop.Metadata

let type_join (t1 t2: option Type): option Type =
  match t1, t2 with
  | Some o1, Some o2 -> Some (o1 & o2)
  | None, o2 -> o2
  | o1, None -> o1

let option_type_sem (t: option Type): Type =
  match t with
  | Some t -> t
  | None   -> unit

let type_join_fst (#t1 #t2: option Type) (v: option_type_sem (type_join t1 t2)): option_type_sem t1 =
 match t1, t2 with
  | Some o1, Some o2 -> fst #(option_type_sem t1) #(option_type_sem t2) v
  | None, o2 -> ()
  | o1, None -> v

let type_join_snd (#t1 #t2: option Type) (v: option_type_sem (type_join t1 t2)): option_type_sem t2 =
 match t1, t2 with
  | Some o1, Some o2 -> snd #(option_type_sem t1) #(option_type_sem t2) v
  | None, o2 -> v
  | o1, None -> ()

let type_join_tup (#t1 #t2: option Type) (v1: option_type_sem t1) (v2: option_type_sem t2): option_type_sem (type_join t1 t2) =
 match t1, t2 with
  | Some o1, Some o2 -> (v1, v2)
  | None, o2 -> v2
  | o1, None -> v1

let prop_join (o1 o2: option prop): option prop =
  match o1, o2 with
  | Some o1, Some o2 -> Some (o1 /\ o2)
  | None, o2 -> o2
  | o1, None -> o1

let option_prop_sem (t: option prop): prop =
  match t with
  | Some t -> t
  | None   -> True


noeq type checks = {
  assumptions: option prop;
  obligations: option prop;
}

noeq
type step_result (state: option Type) (result: Type) = {
  s:    option_type_sem state;
  v:    result;
  chck: checks;
}

(* Step functions are relations so that we can express contracts, which are underspecified.
   The recursive dependency for recursive binders XMu is easier to express as a
   relation too. The result type is `prop`, rather than a computational boolean,
   because composing the relations requires existential quantifiers. *)
noeq
type system (input: Type) (oracle: option Type) (state: option Type) (result: Type) = {
  init: option_type_sem state;

  step:
    (* Values of input variables *)
    i: input ->
    o: option_type_sem oracle ->
    (* Starting state *)
    s: option_type_sem state ->
    step_result state result;
}

let checks_none: checks = {
  assumptions = None;
  obligations = None;
}

let checks_assumption (f: prop): checks = {
  assumptions = Some f;
  obligations = None;
}

let checks_obligation (f: prop): checks = {
  assumptions = None;
  obligations = Some f;
}

let checks_of_prop (status: PM.prop_status) (f: prop): checks =
  match status with
  | PM.PSValid   -> checks_assumption f
  | PM.PSUnknown -> checks_obligation f

let checks_join (c1 c2: checks): checks = {
  assumptions = prop_join c1.assumptions c2.assumptions;
  obligations = prop_join c1.obligations c2.obligations;
}

// let rec system_steps
//   (#input #oracle #result: Type)
//   (#state: option Type)
//   (t: system input oracle state result)
//   (inputs: list (input & oracle & option_type_sem state & result))
//   (s': option_type_sem state): prop =
//   match inputs with
//   | [] -> t.init == s'
//   | ((i, o, s, r) :: inputs') ->
//     system_steps t inputs' s /\
//     t.step i s s' r


// let rec system_stepn
//   (#input #state #result: Type)
//   (t: system input state result)
//   (inputs: list (input & result))
//   (s': state): prop =
//   match inputs with
//   | [] -> t.init s'
//   | ((row, r) :: inputs') ->
//     exists (s0: state).
//     system_stepn t inputs' s0 /\
//     t.step row s0 s' r

let system_const (#input #result: Type) (v: result): system input None None result =
  { init = ();
    step = (fun i o s -> { s = (); v = v; chck = checks_none; });
  }

let system_check (#input: Type) (#oracle #state: option Type)
  (name: string)
  (status: PM.prop_status)
  (t1: system input oracle state bool):
       system input oracle state unit =
  { init = t1.init;
    step = (fun i o s ->
      let s1 = t1.step i o s in
      {
        s = s1.s;
        v = ();
        chck = s1.chck `checks_join` checks_of_prop status (s1.v == true);
      });
  }

let system_contract_instance (#input: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (status: PM.prop_status)
  (tr: system input oracle1 state1 bool)
  (tg: system ('a & input) oracle2 state2 bool):
       system input (Some 'a `type_join` (oracle1 `type_join` oracle2)) (state1 `type_join` state2) 'a =
  { init = tr.init `type_join_tup` tg.init;
    step = (fun i vo s ->
        let v  = type_join_fst vo in
        let o  = type_join_snd vo in
        let o1 = type_join_fst o in
        let o2 = type_join_snd o in
        let s1 = type_join_fst s in
        let s2 = type_join_snd s in
        let stp1 = tr.step     i  o1 s1 in
        let stp2 = tg.step (v, i) o2 s2 in
        let rprop = stp1.v == true in
        let gprop = stp2.v == true in
        {
          s    = type_join_tup stp1.s stp2.s;
          v    = v;
          chck = checks_assumption (rprop ==> gprop) `checks_join`
                 checks_of_prop status rprop `checks_join`
                 stp1.chck `checks_join` stp2.chck;
        });
  }

let system_contract_definition (#input: Type)
  (#oracle1 #oracle2 #oracle3 #state1 #state2 #state3: option Type)
  (tr: system input oracle1 state1 bool)
  (tg: system ('a & input) oracle2 state2 bool)
  (ti: system input oracle3 state3 'a):
       system input (oracle1 `type_join` (oracle2 `type_join` oracle3)) (state1 `type_join` (state2 `type_join` state3)) 'a =
  { init = tr.init `type_join_tup` (tg.init `type_join_tup` ti.init);
    step = (fun i o s ->
        let o1 = type_join_fst o in
        let o2 = type_join_fst (type_join_snd o) in
        let o3 = type_join_snd (type_join_snd o) in
        let s1 = type_join_fst s in
        let s2 = type_join_fst (type_join_snd s) in
        let s3 = type_join_snd (type_join_snd s) in

        let stp3 = ti.step i o3 s3 in
        let v    = stp3.v          in
        let stp1 = tr.step i o1 s1 in
        let stp2 = tg.step (v, i) o2 s2 in
        let rprop = stp1.v == true in
        let gprop = stp2.v == true in
        {
          s = stp1.s `type_join_tup` (stp2.s `type_join_tup` stp3.s);
          v = v;
          chck = checks_obligation gprop `checks_join`
                 checks_assumption rprop `checks_join`
                 stp1.chck `checks_join` stp2.chck `checks_join` stp3.chck;
        });
  }

let system_project (#input #result: Type) (f: input -> result):
       system input None None result =
  { init = ();
    step = (fun i o s ->
      {
        s = ();
        v = f i;
        chck = checks_none;
      });
  }

let system_with_input (#input #input' #result: Type)
    (#oracle #state: option Type)
    (f: input' -> input)
    (t: system input oracle state result):
        system input' oracle state result =
  { init = t.init;
    step = (fun i o s -> t.step (f i) o s);
  }

let system_pre (#input #value: Type)
  (#oracle #state: option Type)
  (init: value)
  (t1: system input oracle state value):
       system input oracle (Some value `type_join` state) value =
  { init = type_join_tup init t1.init;
    step = (fun i o sv ->
      let v  = type_join_fst sv in
      let s1 = type_join_snd sv in
      let stp1 = t1.step i o s1 in
      {
        s = type_join_tup stp1.v stp1.s;
        v = v;
        chck = stp1.chck;
      });
  }

let system_mu (#input #input' #value: Type)
  (#oracle #state: option Type)
  (extend: input -> value -> input')
  (t1: system input' oracle state value):
       system input (Some value `type_join` oracle) state value =
  { init = t1.init;
    step = (fun i vo s ->
      let v = type_join_fst vo in
      let o = type_join_snd vo in
      let stp1 = t1.step (extend i v) o s in
      {
        s = stp1.s;
        v = v;
        chck = checks_assumption (v == stp1.v) `checks_join` stp1.chck;
      });
  }

let system_let (#input #input' #v1 #v2: Type)
  (#oracle1 #oracle2 #state1 #state2: option Type)
  (extend: input -> v1 -> input')
  (t1: system input oracle1 state1 v1)
  (t2: system input' oracle2 state2 v2):
       system input (oracle1 `type_join` oracle2) (state1 `type_join` state2) v2 =
  { init = type_join_tup t1.init t2.init;
    step = (fun i o s ->
      let o1 = type_join_fst o in
      let o2 = type_join_snd o in
      let s1 = type_join_fst s in
      let s2 = type_join_snd s in
      let stp1 = t1.step i o1 s1 in
      let stp2 = t2.step (extend i stp1.v) o2 s2 in
      {
        s = type_join_tup stp1.s stp2.s;
        v = stp2.v;
        chck = stp1.chck `checks_join` stp2.chck;
      });
  }
