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

(* Trivial pointwise pre/postconditions (always [True]). *)
let ptrue_pre (#input: Type) : input -> nat -> prop = fun _ _ -> True
let ptrue_post (#input #output: Type) : input -> output -> nat -> prop = fun _ _ _ -> True

(* System-valued triple = single-system validity of the internalised contract
   [S.contract pre t post]. Its assumptions ([pre]'s value and all three
   subsystems' own assumptions) hold so far implies its obligations ([post]'s
   value and all three subsystems' obligations) hold so far. This matches Pipit's
   [system_contract_definition] / [contract_valid] semantics: [pre]'s and [post]'s
   internal checks are handled *inside* the contract, so there are no external
   side-conditions and [pre]/[post] may themselves carry oracles. *)
let triple
  (#input #output: Type)
  (pre: S.sys input prop)
  (t: S.sys input output)
  (post: S.sys (input & output) prop)
  : prop
  =
  L.triple (L.pw_pre (ptrue_pre #input))
           (S.contract pre t post)
           (L.pw_post (ptrue_post #input #output))

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

(* Base/step VCs = [Logic.base_case]/[Logic.step_case] on the internalised
   contract system with trivial pointwise pre/post. The contract's obligation
   (post's value and t's/pre's/post's obligations) is the goal; its assumptions
   (pre's value and t's/pre's/post's assumptions) are the hypotheses — so pre's
   and post's own checks show up here automatically. *)
let base_case_sys
  (#input #output: Type)
  (pre: S.sys input prop) (t: S.sys input output) (post: S.sys (input & output) prop)
  : prop
  = L.base_case (S.contract pre t post).raw (ptrue_pre #input) (ptrue_post #input #output)

let step_case_sys
  (#input #output: Type)
  (pre: S.sys input prop) (t: S.sys input output) (post: S.sys (input & output) prop)
  : prop
  = L.step_case (S.contract pre t post).raw (ptrue_pre #input) (ptrue_post #input #output)

(* 1-induction: discharge the triple from the base/step VCs over the contract
   system. Pre's assumptions appear as induction hypotheses and post's value as
   an induction goal, exactly as in a direct [induct1] on the contract. *)
let induct1_sys
  (#input #output: Type)
  (pre: S.sys input prop) (t: S.sys input output) (post: S.sys (input & output) prop)
  : Lemma
    (requires base_case_sys pre t post /\ step_case_sys pre t post)
    (ensures triple pre t post)
  = L.induct1_pw (S.contract pre t post) (ptrue_pre #input) (ptrue_post #input #output)

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

(*** SL-level rewriting: transport a triple along an equivalence on the program ***)

(* Output/assumption/obligation congruence for one system on two io-streams that
   agree pointwise. *)
let cong3
  (#i #o: Type) (#oc #st: option Type)
  (sys: SB.system i oc st o) (j1 j2: S.io_stream i oc) (k: nat)
  : Lemma (requires (forall (m: nat). j1 m == j2 m))
          (ensures
            S.stream_of_output sys j1 k == S.stream_of_output sys j2 k /\
            (S.stream_of_assumptions sys j1 k <==> S.stream_of_assumptions sys j2 k) /\
            (S.stream_of_obligations sys j1 k <==> S.stream_of_obligations sys j2 k))
  =
  S.lemma_stream_of_output_congruence      sys j1 j2 k;
  S.lemma_stream_of_assumptions_congruence sys j1 j2 k;
  S.lemma_stream_of_obligations_congruence sys j1 j2 k

(* Contract congruence in the program. Rewriting [t] by an observational
   equivalence rewrites the whole contract. Using [t'' = { t' with oracle =
   t.oracle }] (which equals [t'] and whose oracle reduces to [t.oracle]) makes
   both contracts share the [t]-projection, so [equiv t t'] transfers directly. *)
#push-options "--split_queries always --z3rlimit 300 --fuel 2 --ifuel 1"
let lemma_equiv_contract_t
  (#input #output: Type)
  (pre: S.sys input prop)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  (post: S.sys (input & output) prop)
  : Lemma
    (requires SEq.equiv t t')
    (ensures SEq.equiv (S.contract pre t post) (S.contract pre t' post))
  =
  let t'' : S.sys input output = { t' with oracle = t.oracle } in
  let c   = S.contract pre t   post in
  let c'' = S.contract pre t'' post in
  let aux (is: E.stream input) (orc: E.stream (SB.option_type_sem c.oracle)) (n: nat)
    : Lemma (
        let ios  = S.with_oracle c   is orc in
        let ios' = S.with_oracle c'' is orc in
        S.stream_of_output c.raw ios n == S.stream_of_output c''.raw ios' n /\
        (S.stream_of_assumptions c.raw ios n <==> S.stream_of_assumptions c''.raw ios' n) /\
        (S.stream_of_obligations c.raw ios n <==> S.stream_of_obligations c''.raw ios' n))
    =
    assert (t'' == t');
    let ios  = S.with_oracle c   is orc in
    let ios' = S.with_oracle c'' is orc in
    S.lemma_system_contract pre.raw t.raw   post.raw ios  n;
    S.lemma_system_contract pre.raw t''.raw post.raw ios' n;
    let tios  = S.contract_ios_t #input #output #pre.oracle #t.oracle #post.oracle ios  in
    let tios' = S.contract_ios_t #input #output #pre.oracle #t.oracle #post.oracle ios' in
    let pios  = S.contract_ios_p #input #output #pre.oracle #t.oracle #post.oracle ios  in
    let pios' = S.contract_ios_p #input #output #pre.oracle #t.oracle #post.oracle ios' in
    let qios  = S.contract_ios_q #input #output #pre.oracle #t.oracle #post.oracle #t.state   t.raw   ios  in
    let qios' = S.contract_ios_q #input #output #pre.oracle #t.oracle #post.oracle #t''.state t''.raw ios' in
    (* [ios == ios'] (the two contracts share oracle/state layout in the shared
       [t.oracle]), so [pre]/[t] projections coincide. *)
    assert (forall (k: nat). ios k == ios' k /\ tios k == tios' k /\ pios k == pios' k);
    (* [t] and [t''] agree on the shared [t]-projection (from [equiv], via the
       [with_oracle] form). *)
    introduce forall (k: nat).
        (S.stream_of_output      t.raw tios k == S.stream_of_output      t''.raw tios' k) /\
        (S.stream_of_assumptions t.raw tios k <==> S.stream_of_assumptions t''.raw tios' k) /\
        (S.stream_of_obligations t.raw tios k <==> S.stream_of_obligations t''.raw tios' k)
      with begin
        let js : E.stream input = fun m -> fst (tios m) in
        let jo : E.stream (SB.option_type_sem t.oracle) = fun m -> snd (tios m) in
        SEq.equiv_elim t t'' js jo k;
        cong3 t.raw   (S.with_oracle t   js jo) tios  k;
        cong3 t''.raw (S.with_oracle t'' js jo) tios' k
      end;
    (* Equal [t]-outputs mean [post] is fed the same pair. *)
    assert (forall (k: nat). qios k == qios' k);
    introduce forall (k: nat).
        (S.stream_of_output      post.raw qios k == S.stream_of_output      post.raw qios' k) /\
        (S.stream_of_assumptions post.raw qios k <==> S.stream_of_assumptions post.raw qios' k) /\
        (S.stream_of_obligations post.raw qios k <==> S.stream_of_obligations post.raw qios' k)
      with cong3 post.raw qios qios' k;
    introduce forall (k: nat).
        (S.stream_of_output      pre.raw pios k == S.stream_of_output      pre.raw pios' k) /\
        (S.stream_of_assumptions pre.raw pios k <==> S.stream_of_assumptions pre.raw pios' k) /\
        (S.stream_of_obligations pre.raw pios k <==> S.stream_of_obligations pre.raw pios' k)
      with cong3 pre.raw pios pios' k
  in
  Classical.forall_intro_3 aux
#pop-options

(* Transport a triple along an observational equivalence on the program. *)
let equiv_transport_sys
  (#input #output: Type)
  (pre: S.sys input prop)
  (t: S.sys input output)
  (t': S.sys input output { t'.oracle == t.oracle })
  (post: S.sys (input & output) prop)
  : Lemma
    (requires SEq.equiv t t' /\ triple pre t' post)
    (ensures triple pre t post)
  =
  lemma_equiv_contract_t pre t t' post;
  equiv_transport
    (L.pw_pre (ptrue_pre #input))
    (S.contract pre t  post)
    (S.contract pre t' post)
    (L.pw_post (ptrue_post #input #output))

(*** Rule of consequence: weaken a [map g id] postcondition ***)

(* Postcondition consequence for value-only postconditions [map g id]. Since
   [map g id] carries no oracle/state and no checks of its own, the two contract
   systems [contract pre t (map g id)] and [contract pre t (map g' id)] share
   oracle/state and every [pre]/[t]/[post] io-projection; they differ only in the
   post *value* ([g] vs [g']) inside the obligation. So a pointwise implication
   [g ==> g'] weakens the triple, matching the [Logic]-level rule of consequence
   applied to the internalised contract. *)
#push-options "--split_queries always --z3rlimit 300 --fuel 2 --ifuel 1"
let consequence_post_map
  (#input #output: Type)
  (pre: S.sys input prop)
  (t: S.sys input output)
  (g g': (input & output) -> prop)
  : Lemma
    (requires
      triple pre t (S.map g S.id) /\
      (forall (io: input & output). g io ==> g' io))
    (ensures triple pre t (S.map g' S.id))
  =
  let cg  = S.contract pre t (S.map g  S.id) in
  let cg' = S.contract pre t (S.map g' S.id) in
  (* [with_oracle] ignores the system, so the two contracts' io-streams coincide
     (they share the same oracle). *)
  let aux
    (is: E.stream input)
    (orc: E.stream (SB.option_type_sem cg'.oracle))
    (n: nat)
    : Lemma
      (requires (
        let ios' = S.with_oracle cg' is orc in
        ES.sofar (L.pw_pre (ptrue_pre #input) is) n /\
        ES.sofar (S.stream_of_assumptions cg'.raw ios') n))
      (ensures (
        let ios' = S.with_oracle cg' is orc in
        let os   = S.stream_of_output cg'.raw ios' in
        ES.sofar (L.pw_post (ptrue_post #input #output) is os) n /\
        ES.sofar (S.stream_of_obligations cg'.raw ios') n))
    =
    let ios  : S.io_stream input cg.oracle  = S.with_oracle cg  is orc in
    let ios' : S.io_stream input cg'.oracle = S.with_oracle cg' is orc in
    (* [ios] and [ios'] are the same [fun m -> (is m, orc m)]. *)
    assert (forall (m: nat). ios m == ios' m);
    (* Per step: [cg']'s assumptions imply [cg]'s, and [cg]'s obligations imply
       [cg']'s. Only the post *value* ([g] vs [g']) differs; [g ==> g'] weakens
       the obligation, and the shared [map]-posts contribute equal (trivial)
       checks. *)
    introduce forall (k: nat).
        (S.stream_of_assumptions cg'.raw ios' k ==> S.stream_of_assumptions cg.raw ios k) /\
        (S.stream_of_obligations cg.raw ios k ==> S.stream_of_obligations cg'.raw ios' k)
      with begin
        S.lemma_system_contract pre.raw t.raw (S.map g  S.id).raw ios  k;
        S.lemma_system_contract pre.raw t.raw (S.map g' S.id).raw ios' k;
        let pios  = S.contract_ios_p #input #output #pre.oracle #t.oracle #(S.map g  S.id).oracle ios  in
        let pios' = S.contract_ios_p #input #output #pre.oracle #t.oracle #(S.map g' S.id).oracle ios' in
        let tios  = S.contract_ios_t #input #output #pre.oracle #t.oracle #(S.map g  S.id).oracle ios  in
        let tios' = S.contract_ios_t #input #output #pre.oracle #t.oracle #(S.map g' S.id).oracle ios' in
        let qios  = S.contract_ios_q #input #output #pre.oracle #t.oracle #(S.map g  S.id).oracle #t.state t.raw ios  in
        let qios' = S.contract_ios_q #input #output #pre.oracle #t.oracle #(S.map g' S.id).oracle #t.state t.raw ios' in
        cong3 pre.raw pios pios' k;
        cong3 t.raw   tios tios' k;
        (* [map g id] / [map g' id]: output is [g]/[g'] of [id]'s output (the
           input pair), assumptions/obligations are [id]'s (trivial). *)
        S.lemma_map g  (S.id #(input & output)) qios  k;
        S.lemma_map g' (S.id #(input & output)) qios' k;
        S.lemma_system_project (fun (i: input & output) -> i) qios  k;
        S.lemma_system_project (fun (i: input & output) -> i) qios' k
      end;
    (* [cg]'s assumptions hold so far, so [triple pre t (map g id)] fires. *)
    assert (ES.sofar (S.stream_of_assumptions cg.raw ios) n);
    assert (L.triple (L.pw_pre (ptrue_pre #input)) cg (L.pw_post (ptrue_post #input #output)));
    assert (ES.sofar (S.stream_of_obligations cg.raw ios) n);
    assert (ES.sofar (S.stream_of_obligations cg'.raw ios') n)
  in
  Classical.forall_intro_3 (fun is orc n -> Classical.move_requires (aux is orc) n)
#pop-options

