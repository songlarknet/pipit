(* System-valued specification layer over the extensional stream logic.

   Preconditions and postconditions are *deterministic* (oracle-free) systems
   whose output type is [prop]. Such a system's observable output is a function
   of the input prefix alone, so — unlike an arbitrary [stream -> stream prop] —
   it is causal *by construction*. [triple] is defined in terms of the stream
   [Logic.triple], so the full stream logic remains available as a fallback, and
   every rule's causality side-condition is discharged for free here. *)
module Pipit.Extensional.System.Logic

module E  = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module S  = Pipit.Extensional.System
module SB = Pipit.System.Base
module L  = Pipit.Extensional.Logic
module SEq = Pipit.Extensional.System.Eq
module Classical = FStar.Classical

(* A deterministic (oracle-free) system. Its output is a function of the input. *)
let dsys (input output: Type) = p: S.sys input output { p.oracle == None }

(* Observable output of a deterministic system on an input stream (the empty
   oracle stream is the unique [stream unit]). *)
unfold
let outputs_det
  (#input #output: Type)
  (p: dsys input output)
  (is: E.stream input)
  : E.stream output
  =
  S.stream_of_output p.raw (S.with_oracle p is (fun (_: nat) -> ()))

(* Decode a prop-valued precondition system into a stream predicate. *)
unfold
let spred
  (#input: Type)
  (p: dsys input prop)
  : E.stream input -> E.stream prop
  =
  fun is -> outputs_det p is

(* Pair two streams pointwise. Named (not inlined) so the postcondition input
   stream is a single shared term everywhere it appears. *)
let pair_streams (#a #b: Type) (xs: E.stream a) (ys: E.stream b) : E.stream (a & b) =
  fun n -> (xs n, ys n)

(* Decode a prop-valued postcondition system (over paired input & output) into a
   two-stream predicate. *)
unfold
let spred2
  (#input #output: Type)
  (q: dsys (input & output) prop)
  : E.stream input -> E.stream output -> E.stream prop
  =
  fun is os -> outputs_det q (pair_streams is os)

(* System-valued triple. The pre/postconditions are ordinary systems; [triple]
   only decodes them when they are deterministic (oracle-free), so the guards
   make it stateable over any [sys] while [induct1_sys] carries [oracle == None]
   as a precondition. For oracle-free specs (the usual case) the guards vanish
   and this is exactly [Logic.triple] on the decoded predicates. *)
unfold
let triple
  (#input #output: Type)
  (pre: S.sys input prop)
  (t: S.sys input output)
  (post: S.sys (input & output) prop)
  : prop
  =
  pre.oracle == None ==>
  post.oracle == None ==>
  L.triple (spred pre) t (spred2 post)

(*** Causality is free ***)

(* A decoded precondition is causal: its value at [n] is the system output at
   [n], which depends only on the input prefix. *)
let lemma_spred_causal
  (#input: Type)
  (p: dsys input prop)
  : Lemma (ES.causal (spred p))
  =
  introduce forall (is1 is2: E.stream input) (n: nat).
      (forall (k: nat). k <= n ==> is1 k == is2 k) ==>
      (spred p is1 n <==> spred p is2 n)
  with introduce _ ==> _ with _.
       S.lemma_stream_of_output_congruence p.raw
         (S.with_oracle p is1 (fun (_: nat) -> ()))
         (S.with_oracle p is2 (fun (_: nat) -> ()))
         n

(* A decoded postcondition is causal2. *)
let lemma_spred2_causal2
  (#input #output: Type)
  (q: dsys (input & output) prop)
  : Lemma (ES.causal2 (spred2 q))
  =
  introduce forall (is1 is2: E.stream input) (os1 os2: E.stream output) (n: nat).
      (forall (k: nat). k <= n ==> is1 k == is2 k) ==>
      (forall (k: nat). k <= n ==> os1 k == os2 k) ==>
      (spred2 q is1 os1 n <==> spred2 q is2 os2 n)
  with introduce _ ==> _ with _.
       introduce _ ==> _ with _.
       S.lemma_stream_of_output_congruence q.raw
         (S.with_oracle q (pair_streams is1 os1) (fun (_: nat) -> ()))
         (S.with_oracle q (pair_streams is2 os2) (fun (_: nat) -> ()))
         n

(*** Transition-system 1-induction for system-valued triples ***)

(* One step of the product [pre | t | post]: run [t] (output [rt.v], checks),
   run the precondition [pre] (rely [rp.v]) and the postcondition [post] on the
   paired input & [t]-output (guarantee [rq.v]). *)

(* Base case body at an initial input/oracle. *)
let base_case_sys_body
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  (i: input) (o: SB.option_type_sem t.oracle)
  : prop
  =
  let rt = t.raw.step i o t.raw.init in
  let rp = pre.raw.step i () pre.raw.init in
  let rq = post.raw.step (i, rt.v) () post.raw.init in
  rp.v ==>
  SB.option_prop_sem rt.chck.assumptions ==>
  (rq.v /\ SB.option_prop_sem rt.chck.obligations)

let base_case_sys
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  : prop
  =
  forall (i: input) (o: SB.option_type_sem t.oracle). base_case_sys_body pre t post i o

(* Step case body (abstract states [sp]/[st]/[sq]): if rely and guarantee held at
   the current step, and rely holds at the next, the guarantee holds next too. *)
let step_case_sys_body
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  (sp: SB.option_type_sem pre.state)
  (st: SB.option_type_sem t.state)
  (sq: SB.option_type_sem post.state)
  (i0: input) (o0: SB.option_type_sem t.oracle)
  (i1: input) (o1: SB.option_type_sem t.oracle)
  : prop
  =
  let rt0 = t.raw.step i0 o0 st in
  let rp0 = pre.raw.step i0 () sp in
  let rq0 = post.raw.step (i0, rt0.v) () sq in
  let rt1 = t.raw.step i1 o1 rt0.s in
  let rp1 = pre.raw.step i1 () rp0.s in
  let rq1 = post.raw.step (i1, rt1.v) () rq0.s in
  rp0.v ==>
  SB.option_prop_sem rt0.chck.assumptions ==>
  rq0.v ==>
  SB.option_prop_sem rt0.chck.obligations ==>
  rp1.v ==>
  SB.option_prop_sem rt1.chck.assumptions ==>
  (rq1.v /\ SB.option_prop_sem rt1.chck.obligations)

let step_case_sys
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  : prop
  =
  forall (sp: SB.option_type_sem pre.state)
         (st: SB.option_type_sem t.state)
         (sq: SB.option_type_sem post.state)
         (i0: input) (o0: SB.option_type_sem t.oracle)
         (i1: input) (o1: SB.option_type_sem t.oracle).
    step_case_sys_body pre t post sp st sq i0 o0 i1 o1

(* [stream_of_output] at [n] is the step result's value (proved fuel-free, so it
   survives the [fuel 2] context of the induction below without step_result_at
   unfolding to mismatched depths). *)
let lemma_out_v
  (#input #result: Type) (#oracle #state: option Type)
  (t: SB.system input oracle state result) (ios: S.io_stream input oracle) (n: nat)
  : Lemma (S.stream_of_output t ios n == (S.step_result_at t ios n).v)
  = ()

let lemma_asm_v
  (#input #result: Type) (#oracle #state: option Type)
  (t: SB.system input oracle state result) (ios: S.io_stream input oracle) (n: nat)
  : Lemma (S.stream_of_assumptions t ios n ==
           SB.option_prop_sem (S.step_result_at t ios n).chck.assumptions)
  = ()

let lemma_obl_v
  (#input #result: Type) (#oracle #state: option Type)
  (t: SB.system input oracle state result) (ios: S.io_stream input oracle) (n: nat)
  : Lemma (S.stream_of_obligations t ios n ==
           SB.option_prop_sem (S.step_result_at t ios n).chck.obligations)
  = ()

(* [spred]/[spred2] at [n] as the corresponding system's step-result value. *)
let lemma_spred_v
  (#input: Type) (p: dsys input prop) (is: E.stream input) (n: nat)
  : Lemma (spred p is n ==
           (S.step_result_at p.raw (S.with_oracle p is (fun (_: nat) -> ())) n).v)
  = ()

let lemma_spred2_v
  (#input #output: Type) (q: dsys (input & output) prop)
  (is: E.stream input) (os: E.stream output) (n: nat)
  : Lemma (spred2 q is os n ==
           (S.step_result_at q.raw (S.with_oracle q (pair_streams is os) (fun (_: nat) -> ())) n).v)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 600"

let elim_base_case_sys
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  (i: input) (o: SB.option_type_sem t.oracle)
  : Lemma (requires base_case_sys pre t post)
          (ensures base_case_sys_body pre t post i o)
  =
  eliminate forall (j: input) (p: SB.option_type_sem t.oracle). base_case_sys_body pre t post j p
    with i o

let elim_step_case_sys
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  (sp: SB.option_type_sem pre.state)
  (st: SB.option_type_sem t.state)
  (sq: SB.option_type_sem post.state)
  (i0: input) (o0: SB.option_type_sem t.oracle)
  (i1: input) (o1: SB.option_type_sem t.oracle)
  : Lemma (requires step_case_sys pre t post)
          (ensures step_case_sys_body pre t post sp st sq i0 o0 i1 o1)
  =
  eliminate
    forall (sp': SB.option_type_sem pre.state)
           (st': SB.option_type_sem t.state)
           (sq': SB.option_type_sem post.state)
           (j0: input) (p0: SB.option_type_sem t.oracle)
           (j1: input) (p1: SB.option_type_sem t.oracle).
      step_case_sys_body pre t post sp' st' sq' j0 p0 j1 p1
    with sp st sq i0 o0 i1 o1

(* Soundness: strong induction on the step index, threading the three system
   states. The consecutive [pre]/[t]/[post] steps at [n-1] and [n] are exposed
   (fuel 2) in fully-nested form so the base/step cases instantiate. *)
let rec induct1_sys_aux
  (#input #output: Type)
  (pre: dsys input prop) (t: S.sys input output) (post: dsys (input & output) prop)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem t.oracle))
  (n: nat)
  : Lemma
    (requires
      base_case_sys pre t post /\
      step_case_sys pre t post /\
      ES.sofar (spred pre is) n /\
      ES.sofar (S.stream_of_assumptions t.raw (S.with_oracle t is orc)) n)
    (ensures (
      let t_ios = S.with_oracle t is orc in
      let os = S.stream_of_output t.raw t_ios in
      ES.sofar (spred2 post is os) n /\
      ES.sofar (S.stream_of_obligations t.raw t_ios) n))
    (decreases n)
  =
  let t_ios    = S.with_oracle t is orc in
  let os       = S.stream_of_output t.raw t_ios in
  let pre_ios  = S.with_oracle pre is (fun (_: nat) -> ()) in
  let post_ios = S.with_oracle post (pair_streams is os) (fun (_: nat) -> ()) in
  (if n > 0 then begin
    ES.sofar_weaken (spred pre is) n (n - 1);
    ES.sofar_weaken (S.stream_of_assumptions t.raw t_ios) n (n - 1);
    induct1_sys_aux pre t post is orc (n - 1)
  end);
  ES.sofar_index (spred pre is) n;
  ES.sofar_index (S.stream_of_assumptions t.raw t_ios) n;
  (if n = 0
   then begin
     assert (S.step_result_at t.raw t_ios 0 == t.raw.step (is 0) (orc 0) t.raw.init);
     assert (S.step_result_at pre.raw pre_ios 0 == pre.raw.step (is 0) () pre.raw.init);
     lemma_out_v t.raw t_ios 0;
     lemma_asm_v t.raw t_ios 0;
     lemma_obl_v t.raw t_ios 0;
     assert (S.step_result_at post.raw post_ios 0 ==
       post.raw.step (is 0, os 0) () post.raw.init);
     lemma_spred_v pre is 0;
     lemma_spred2_v post is os 0;
     elim_base_case_sys pre t post (is 0) (orc 0);
     assert (spred2 post is os 0);
     assert (S.stream_of_obligations t.raw t_ios 0)
   end
   else begin
     ES.sofar_index (spred2 post is os) (n - 1);
     ES.sofar_index (S.stream_of_obligations t.raw t_ios) (n - 1);
     let st = (if n = 1 then t.raw.init    else (S.step_result_at t.raw t_ios (n - 2)).s) in
     let sp = (if n = 1 then pre.raw.init  else (S.step_result_at pre.raw pre_ios (n - 2)).s) in
     let sq = (if n = 1 then post.raw.init else (S.step_result_at post.raw post_ios (n - 2)).s) in
     lemma_out_v t.raw t_ios (n - 1);
     lemma_out_v t.raw t_ios n;
     assert (S.step_result_at t.raw t_ios (n - 1) == t.raw.step (is (n - 1)) (orc (n - 1)) st);
     assert (S.step_result_at t.raw t_ios n ==
       t.raw.step (is n) (orc n) (t.raw.step (is (n - 1)) (orc (n - 1)) st).s);
     assert (S.step_result_at pre.raw pre_ios (n - 1) == pre.raw.step (is (n - 1)) () sp);
     assert (S.step_result_at pre.raw pre_ios n ==
       pre.raw.step (is n) () (pre.raw.step (is (n - 1)) () sp).s);
     assert (S.step_result_at post.raw post_ios (n - 1) ==
       post.raw.step (is (n - 1), os (n - 1)) () sq);
     assert (S.step_result_at post.raw post_ios n ==
       post.raw.step (is n, os n) () (post.raw.step (is (n - 1), os (n - 1)) () sq).s);
     (* bridge the step results to the spred / assumption / obligation streams *)
     lemma_spred_v pre is (n - 1);
     lemma_spred_v pre is n;
     lemma_spred2_v post is os (n - 1);
     lemma_spred2_v post is os n;
     lemma_asm_v t.raw t_ios (n - 1);
     lemma_asm_v t.raw t_ios n;
     lemma_obl_v t.raw t_ios (n - 1);
     lemma_obl_v t.raw t_ios n;
     elim_step_case_sys pre t post sp st sq (is (n - 1)) (orc (n - 1)) (is n) (orc n);
     (* [t]'s step output at n-1 / n is [os], so [post]'s input matches *)
     assert ((t.raw.step (is (n - 1)) (orc (n - 1)) st).v == os (n - 1));
     assert ((t.raw.step (is n) (orc n) (t.raw.step (is (n - 1)) (orc (n - 1)) st).s).v == os n);
     assert (spred2 post is os n ==
       (post.raw.step (is n, os n) () (post.raw.step (is (n - 1), os (n - 1)) () sq).s).v);
     assert (spred2 post is os n);
     assert (S.stream_of_obligations t.raw t_ios n)
   end)

let induct1_sys
  (#input #output: Type)
  (pre: S.sys input prop) (t: S.sys input output) (post: S.sys (input & output) prop)
  : Lemma
    (requires pre.oracle == None /\ post.oracle == None /\
              base_case_sys pre t post /\ step_case_sys pre t post)
    (ensures triple pre t post)
  =
  let aux
    (is: E.stream input)
    (orc: E.stream (SB.option_type_sem t.oracle))
    (n: nat)
    : Lemma
      (ensures (
        let t_ios = S.with_oracle t is orc in
        let os = S.stream_of_output t.raw t_ios in
        ES.sofar (spred pre is) n ==>
        ES.sofar (S.stream_of_assumptions t.raw t_ios) n ==>
        (ES.sofar (spred2 post is os) n /\
         ES.sofar (S.stream_of_obligations t.raw t_ios) n)))
    =
    Classical.move_requires (induct1_sys_aux pre t post is orc) n
  in
  Classical.forall_intro_3 aux
#pop-options

(* Decode a [map g id] postcondition system: its stream predicate at [n] is just
   [g] applied to the paired input/output at [n]. Factored out so consequence
   steps over [map]/[id] specs need not unfold [spred2] by hand. *)
let lemma_spred2_map_id
  (#input #output: Type)
  (g: (input & output) -> prop)
  (is: E.stream input) (os: E.stream output) (n: nat)
  : Lemma (spred2 (S.map g S.id) is os n == g (is n, os n))
  =
  let jos = S.with_oracle (S.map g S.id) (pair_streams is os) (fun (_: nat) -> ()) in
  S.lemma_map g (S.id #(input & output)) jos n;
  S.lemma_system_project (fun (i: input & output) -> i) jos n

(*** Transport a triple along an observational equivalence ***)

(* Rewriting rule: if the program [t] is observationally equivalent to [t']
   ([System.Eq.equiv], sharing the oracle type) and the postcondition [q] is
   causal, a triple about [t'] is a triple about [t]. This is how an equational
   rewrite is *applied* to a proof: discharge the property on the convenient
   (e.g. common-subexpression-shared) form [t'], then move it back to [t]. No
   [oracle == None] restriction — [equiv] relates the two systems under the same
   oracle stream, so this transports oracle-carrying systems too. *)
#push-options "--split_queries always --z3rlimit 100"
let equiv_transport
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      ES.causal2 q /\
      L.triple p t' q /\ SEq.equiv t t')
    (ensures L.triple p t q)
  =
  let aux
    (is: E.stream input)
    (orc: E.stream (SB.option_type_sem t.oracle))
    (n: nat)
    : Lemma
      (requires (
        let ios = S.with_oracle t is orc in
        ES.sofar (p is) n /\ ES.sofar (S.stream_of_assumptions t.raw ios) n))
      (ensures (
        let ios = S.with_oracle t is orc in
        let os  = S.stream_of_output t.raw ios in
        ES.sofar (q is os) n /\ ES.sofar (S.stream_of_obligations t.raw ios) n))
    =
    let ios  = S.with_oracle t is orc in
    let ios' = S.with_oracle t' is orc in
    let os   = S.stream_of_output t.raw ios in
    let os'  = S.stream_of_output t'.raw ios' in
    (* [equiv]: [t] on [ios] agrees with [t'] on [ios'] at every step. *)
    introduce forall (k: nat).
        S.stream_of_output t.raw ios k == S.stream_of_output t'.raw ios' k /\
        (S.stream_of_assumptions t.raw ios k <==> S.stream_of_assumptions t'.raw ios' k) /\
        (S.stream_of_obligations t.raw ios k <==> S.stream_of_obligations t'.raw ios' k)
      with SEq.equiv_elim t t' is orc k;
    (* Assumptions transport to [t'], so the [t']-triple fires. *)
    assert (ES.sofar (S.stream_of_assumptions t'.raw ios') n);
    assert (ES.sofar (q is os') n /\ ES.sofar (S.stream_of_obligations t'.raw ios') n);
    (* [os] and [os'] agree pointwise; causality moves [q] back to [os]. *)
    ES.lemma_causal2_prefix q is is os' os n
  in
  Classical.forall_intro_3 (fun is orc n -> Classical.move_requires (aux is orc) n)
#pop-options

(*** Internalise a pre/post into a contract, then prove the triple by validity ***)

(* [spred] of the trivial precondition [const True] holds at every horizon. *)
let lemma_spred_const_true
  (#input: Type) (is: E.stream input) (n: nat)
  : Lemma (ES.sofar (spred (S.const True) is) n)
  =
  S.stream_of_output_system_const True
    (S.with_oracle (S.const #input #prop True) is (fun (_: nat) -> ()))

(* Instantiate a system-valued triple at a chosen input / oracle / step. *)
let triple_elim
  (#input #output: Type)
  (pre: S.sys input prop { pre.oracle == None })
  (t: S.sys input output)
  (post: S.sys (input & output) prop { post.oracle == None })
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem t.oracle))
  (n: nat)
  : Lemma
    (requires triple pre t post)
    (ensures (
      let ios = S.with_oracle t is orc in
      let os  = S.stream_of_output t.raw ios in
      ES.sofar (spred pre is) n ==>
      ES.sofar (S.stream_of_assumptions t.raw ios) n ==>
      (ES.sofar (spred2 post is os) n /\ ES.sofar (S.stream_of_obligations t.raw ios) n)))
  = ()

(* Bridge rule: a triple [{ p } t { q }] holds when the internalised contract
   [contract p t q] is valid, i.e. [{ const True } contract p t q { const True }].
   [p]/[q] are deterministic (oracle-free) and check-free specs; [t] may carry an
   oracle. Internalising folds [p] into the assumptions and [q] into the
   obligations, so the triple becomes validity of a single system — which can
   then be rewritten via [equiv_transport]. *)
#push-options "--split_queries always --z3rlimit 300 --fuel 2 --ifuel 1"
let contract_valid_triple
  (#input #output: Type)
  (p: S.sys input prop { p.oracle == None })
  (t: S.sys input output)
  (q: S.sys (input & output) prop { q.oracle == None })
  : Lemma
    (requires
      (forall (iop: S.io_stream input p.oracle) (k: nat). S.stream_of_assumptions p.raw iop k) /\
      (forall (iop: S.io_stream input p.oracle) (k: nat). S.stream_of_obligations p.raw iop k) /\
      (forall (ioq: S.io_stream (input & output) q.oracle) (k: nat). S.stream_of_assumptions q.raw ioq k) /\
      (forall (ioq: S.io_stream (input & output) q.oracle) (k: nat). S.stream_of_obligations q.raw ioq k) /\
      triple (S.const True) (S.contract p t q) (S.const True))
    (ensures triple p t q)
  =
  let csys = S.contract p t q in
  let aux
    (is: E.stream input)
    (orc_t: E.stream (SB.option_type_sem t.oracle))
    (n: nat)
    : Lemma
      (requires (
        let iot = S.with_oracle t is orc_t in
        ES.sofar (spred p is) n /\ ES.sofar (S.stream_of_assumptions t.raw iot) n))
      (ensures (
        let iot = S.with_oracle t is orc_t in
        let os  = S.stream_of_output t.raw iot in
        ES.sofar (spred2 q is os) n /\ ES.sofar (S.stream_of_obligations t.raw iot) n))
    =
    (* The contract oracle: unit for [p]/[q], [orc_t] for [t]. *)
    let orc_c : E.stream (SB.option_type_sem csys.oracle) =
      fun k -> SB.type_join_tup #p.oracle #(SB.type_join t.oracle q.oracle) ()
                 (SB.type_join_tup #t.oracle #q.oracle (orc_t k) ()) in
    let cios = S.with_oracle csys is orc_c in
    let pios = S.contract_ios_p #input #output #p.oracle #t.oracle #q.oracle cios in
    let tios = S.contract_ios_t #input #output #p.oracle #t.oracle #q.oracle cios in
    let qios = S.contract_ios_q #input #output #p.oracle #t.oracle #q.oracle #t.state t.raw cios in
    let iot   = S.with_oracle t is orc_t in
    let os    = S.stream_of_output t.raw iot in
    let punit = S.with_oracle p is (fun (_: nat) -> ()) in
    let qunit = S.with_oracle q (pair_streams is os) (fun (_: nat) -> ()) in
    (* Oracle projections: [tios] recovers [iot], [pios]/[qios] the unit runs. *)
    introduce forall (k: nat). tios k == iot k /\ pios k == punit k
      with begin
        S.lemma_type_join_snd_tup #p.oracle #(SB.type_join t.oracle q.oracle) ()
          (SB.type_join_tup #t.oracle #q.oracle (orc_t k) ());
        S.lemma_type_join_fst_tup #t.oracle #q.oracle (orc_t k) ();
        S.lemma_type_join_fst_tup #p.oracle #(SB.type_join t.oracle q.oracle) ()
          (SB.type_join_tup #t.oracle #q.oracle (orc_t k) ())
      end;
    (* [t]'s outputs coincide on [tios] and [iot], so [qios] pairs with [os]. *)
    introduce forall (k: nat). S.stream_of_output t.raw tios k == os k
      with S.lemma_stream_of_output_congruence t.raw tios iot k;
    introduce forall (k: nat). qios k == qunit k
      with begin
        S.lemma_type_join_snd_tup #p.oracle #(SB.type_join t.oracle q.oracle) ()
          (SB.type_join_tup #t.oracle #q.oracle (orc_t k) ());
        S.lemma_type_join_snd_tup #t.oracle #q.oracle (orc_t k) ()
      end;
    (* Contract check decomposition + congruence of the sub-runs to the specs. *)
    Classical.forall_intro (S.lemma_system_contract p.raw t.raw q.raw cios);
    introduce forall (k: nat).
        S.stream_of_output p.raw pios k == spred p is k /\
        (S.stream_of_assumptions t.raw tios k <==> S.stream_of_assumptions t.raw iot k) /\
        (S.stream_of_obligations t.raw tios k <==> S.stream_of_obligations t.raw iot k) /\
        S.stream_of_output q.raw qios k == spred2 q is os k
      with begin
        S.lemma_stream_of_output_congruence p.raw pios punit k;
        S.lemma_stream_of_assumptions_congruence t.raw tios iot k;
        S.lemma_stream_of_obligations_congruence t.raw tios iot k;
        S.lemma_stream_of_output_congruence q.raw qios qunit k
      end;
    (* [p]/[q] are check-free, so the contract's assumptions reduce to
       [spred p /\ asm t] and its obligations to [spred2 q /\ obl t]. *)
    ES.sofar_index (spred p is) n;
    ES.sofar_index (S.stream_of_assumptions t.raw iot) n;
    assert (ES.sofar (S.stream_of_assumptions csys.raw cios) n);
    lemma_spred_const_true is n;
    triple_elim (S.const True) csys (S.const True) is orc_c n;
    assert (ES.sofar (S.stream_of_obligations csys.raw cios) n);
    ES.sofar_index (S.stream_of_obligations csys.raw cios) n
  in
  Classical.forall_intro_3 (fun is orc n -> Classical.move_requires (aux is orc) n)
#pop-options



