(* Proofs for the extensional program logic. The user-facing judgement, the
   causality side-conditions, and the [mu] rule's statement are in the
   companion [.fsti]; this module supplies the guarded-recursion proof. *)
module Pipit.Extensional.Logic

module E   = Pipit.Extensional.Base
module ES  = Pipit.Extensional.Stream
module S   = Pipit.Extensional.System
module SB  = Pipit.System.Base

module Classical = FStar.Classical

(* Assemble a [mu]-body input stream from a feedback stream and a source input
   stream. Kept transparent so [source] reduces pointwise to the inputs. *)
let mu_body_input
  (#input #output: Type)
  (fb: E.stream output)
  (is: E.stream input)
  : E.stream (output & input)
  =
  fun n -> (fb n, is n)

(* Auxiliary induction: for a fixed input and oracle stream, every prefix of a
   [mu] run satisfies the postcondition and obligations. *)
#push-options "--z3rlimit 40"
let rec mu_aux
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (body: S.sys (output & input) output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem (S.mu body).oracle))
  (n: nat)
  : Lemma
    (requires
      ES.causal p /\
      ES.causal2 q /\
      triple (mu_body_pre p q) body (mu_body_post q) /\
      ES.sofar (p is) n /\
      ES.sofar (S.stream_of_assumptions (S.mu body).raw (S.with_oracle (S.mu body) is orc)) n)
    (ensures (
      let ios_mu = S.with_oracle (S.mu body) is orc in
      ES.sofar (q is (S.stream_of_output (S.mu body).raw ios_mu)) n /\
      ES.sofar (S.stream_of_obligations (S.mu body).raw ios_mu) n))
    (decreases n)
  =
  let t1       = body.raw in
  let ios_mu   = S.with_oracle (S.mu body) is orc in
  let body_ios = S.mu_body_ios ios_mu in
  let os_mu    = S.stream_of_output (S.mu body).raw ios_mu in
  let fb : E.stream output = fun k -> S.mu_guess ios_mu k in
  let is' : E.stream (output & input) = mu_body_input fb is in
  let orc' : E.stream (SB.option_type_sem body.oracle) =
    fun k -> SB.type_join_snd #(Some output) #body.oracle (snd (ios_mu k)) in
  let ios'     = S.with_oracle body is' orc' in
  let os'      = S.stream_of_output body.raw ios' in

  (* [mu body]'s underlying system is [system_mu] of the body's system. *)
  assert ((S.mu body).raw == SB.system_mu t1);

  (* System [mu] facts, for every step. *)
  Classical.forall_intro (S.lemma_stream_of_output_system_mu t1 ios_mu);
  Classical.forall_intro (S.lemma_stream_of_obligations_system_mu t1 ios_mu);
  Classical.forall_intro (S.lemma_stream_of_assumptions_system_mu t1 ios_mu);

  (* The body triple's io-stream agrees with [mu_body_ios] at every step, so
     outputs / assumptions / obligations agree there too. *)
  assert (forall (k: nat). ios' k == body_ios k);
  introduce forall (k: nat).
      S.stream_of_output body.raw ios' k == S.stream_of_output t1 body_ios k
  with S.lemma_stream_of_output_congruence body.raw ios' body_ios k;
  introduce forall (k: nat).
      S.stream_of_assumptions body.raw ios' k == S.stream_of_assumptions t1 body_ios k
  with S.lemma_stream_of_assumptions_congruence body.raw ios' body_ios k;
  introduce forall (k: nat).
      S.stream_of_obligations body.raw ios' k == S.stream_of_obligations t1 body_ios k
  with S.lemma_stream_of_obligations_congruence body.raw ios' body_ios k;

  (* Source and feedback projections of the chosen body input. *)
  assert (forall (k: nat). source is' k == is k);
  assert (forall (k: nat). feedback is' k == os_mu k);

  (* Induction hypothesis: Q holds so far on the (n-1)-prefix. *)
  (if n > 0 then begin
    ES.sofar_weaken (p is) n (n - 1);
    ES.sofar_weaken (S.stream_of_assumptions (S.mu body).raw ios_mu) n (n - 1);
    mu_aux p body q is orc (n - 1)
  end);

  (* Expose the hypotheses (and, when n>0, the IH) at every step. *)
  ES.sofar_index (p is) n;
  ES.sofar_index (S.stream_of_assumptions (S.mu body).raw ios_mu) n;
  (if n > 0 then ES.sofar_index (q is os_mu) (n - 1));

  (* On the assumption-satisfying prefix, [os_mu] and the body output agree. *)
  assert (forall (k: nat). k <= n ==> os_mu k == os' k);

  (* Causal transports: swap the body's projected input/feedback for the source
     input / [os_mu] on the prefix. *)
  ES.lemma_causal_prefix p (source is') is n;
  ES.lemma_causal2_prefix q (source is') is (feedback is') os_mu n;
  ES.lemma_causal2_prefix q (source is') is os' os_mu n;

  (* Body triple premise 1: the guarded precondition. *)
  assert (forall (k: nat). k <= n ==> p (source is') k);
  assert (forall (k: nat). k <= n ==> ES.pre (q (source is') (feedback is')) k);
  assert (ES.sofar (mu_body_pre p q is') n);
  (* Body triple premise 2: body assumptions. *)
  assert (ES.sofar (S.stream_of_assumptions body.raw ios') n);

  (* Body triple conclusion. *)
  assert (ES.sofar (mu_body_post q is' os') n);
  assert (ES.sofar (S.stream_of_obligations body.raw ios') n);

  (* Transport Q from the body output to [os_mu], and obligations back. *)
  assert (ES.sofar (q is os_mu) n);
  assert (ES.sofar (S.stream_of_obligations (S.mu body).raw ios_mu) n)

let mu #input #output p body q =
  let aux
    (is: E.stream input)
    (orc: E.stream (SB.option_type_sem (S.mu body).oracle))
    (n: nat)
    : Lemma
      (ensures (
        let ios = S.with_oracle (S.mu body) is orc in
        ES.sofar (p is) n ==>
        ES.sofar (S.stream_of_assumptions (S.mu body).raw ios) n ==>
        (ES.sofar (q is (S.stream_of_output (S.mu body).raw ios)) n /\
         ES.sofar (S.stream_of_obligations (S.mu body).raw ios) n)))
    =
    Classical.move_requires (mu_aux p body q is orc) n
  in
  Classical.forall_intro_3 aux
#pop-options

(* [fby v0 t] only shifts the output ([lemma_system_pre]: checks unchanged), so a
   triple about [t] with [q] post-composed with [ES.fby v0] transfers, after a
   [causal2] transport to swap the (pointwise-equal) output streams. *)
#push-options "--z3rlimit 40"
let fby_aux
  (#input #output: Type)
  (v0: output)
  (t: S.sys input output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem (S.fby v0 t).oracle))
  (n: nat)
  : Lemma
    (requires
      ES.causal2 q /\
      triple p t (fun is ot -> q is (ES.fby v0 ot)) /\
      ES.sofar (p is) n /\
      ES.sofar (S.stream_of_assumptions (S.fby v0 t).raw (S.with_oracle (S.fby v0 t) is orc)) n)
    (ensures (
      let ios = S.with_oracle (S.fby v0 t) is orc in
      ES.sofar (q is (S.stream_of_output (S.fby v0 t).raw ios)) n /\
      ES.sofar (S.stream_of_obligations (S.fby v0 t).raw ios) n))
  =
  let ios   = S.with_oracle (S.fby v0 t) is orc in
  let ios_t = S.with_oracle t is orc in
  let ot    = S.stream_of_output t.raw ios_t in
  let os_f  = S.stream_of_output (S.fby v0 t).raw ios in
  assert (forall (k: nat). ios k == ios_t k);
  assert ((S.fby v0 t).raw == SB.system_pre v0 t.raw);
  Classical.forall_intro (S.lemma_system_pre v0 t.raw ios);
  introduce forall (k: nat). S.stream_of_output t.raw ios k == ot k
    with S.lemma_stream_of_output_congruence t.raw ios ios_t k;
  introduce forall (k: nat).
      S.stream_of_assumptions t.raw ios k == S.stream_of_assumptions t.raw ios_t k
    with S.lemma_stream_of_assumptions_congruence t.raw ios ios_t k;
  introduce forall (k: nat).
      S.stream_of_obligations t.raw ios k == S.stream_of_obligations t.raw ios_t k
    with S.lemma_stream_of_obligations_congruence t.raw ios ios_t k;
  assert (forall (k: nat). os_f k == ES.fby v0 ot k);
  assert (ES.sofar (S.stream_of_assumptions t.raw ios_t) n);
  assert (ES.sofar (q is (ES.fby v0 ot)) n);
  assert (ES.sofar (S.stream_of_obligations t.raw ios_t) n);
  ES.lemma_causal2_prefix q is is (ES.fby v0 ot) os_f n;
  assert (ES.sofar (q is os_f) n);
  assert (ES.sofar (S.stream_of_obligations (S.fby v0 t).raw ios) n)

let fby #input #output v0 t p q =
  Classical.forall_intro_3
    (fun is orc n -> Classical.move_requires (fby_aux v0 t p q is orc) n)

(* [map f t] only transforms the output ([lemma_system_map_result]: checks
   unchanged); same rewrite + [causal2] transport as [fby]. *)
let map_aux
  (#input #output1 #output2: Type)
  (f: output1 -> output2)
  (t: S.sys input output1)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output2 -> E.stream prop)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem (S.map f t).oracle))
  (n: nat)
  : Lemma
    (requires
      ES.causal2 q /\
      triple p t (fun is ot -> q is (ES.map f ot)) /\
      ES.sofar (p is) n /\
      ES.sofar (S.stream_of_assumptions (S.map f t).raw (S.with_oracle (S.map f t) is orc)) n)
    (ensures (
      let ios = S.with_oracle (S.map f t) is orc in
      ES.sofar (q is (S.stream_of_output (S.map f t).raw ios)) n /\
      ES.sofar (S.stream_of_obligations (S.map f t).raw ios) n))
  =
  let ios   = S.with_oracle (S.map f t) is orc in
  let ios_t = S.with_oracle t is orc in
  let ot    = S.stream_of_output t.raw ios_t in
  let os_m  = S.stream_of_output (S.map f t).raw ios in
  assert (forall (k: nat). ios k == ios_t k);
  assert ((S.map f t).raw == SB.system_map_result f t.raw);
  Classical.forall_intro (S.lemma_system_map_result f t.raw ios);
  introduce forall (k: nat). S.stream_of_output t.raw ios k == ot k
    with S.lemma_stream_of_output_congruence t.raw ios ios_t k;
  introduce forall (k: nat).
      S.stream_of_assumptions t.raw ios k == S.stream_of_assumptions t.raw ios_t k
    with S.lemma_stream_of_assumptions_congruence t.raw ios ios_t k;
  introduce forall (k: nat).
      S.stream_of_obligations t.raw ios k == S.stream_of_obligations t.raw ios_t k
    with S.lemma_stream_of_obligations_congruence t.raw ios ios_t k;
  assert (forall (k: nat). os_m k == ES.map f ot k);
  assert (ES.sofar (S.stream_of_assumptions t.raw ios_t) n);
  assert (ES.sofar (q is (ES.map f ot)) n);
  assert (ES.sofar (S.stream_of_obligations t.raw ios_t) n);
  ES.lemma_causal2_prefix q is is (ES.map f ot) os_m n;
  assert (ES.sofar (q is os_m) n);
  assert (ES.sofar (S.stream_of_obligations (S.map f t).raw ios) n)

let map #input #output1 #output2 f t p q =
  Classical.forall_intro_3
    (fun is orc n -> Classical.move_requires (map_aux f t p q is orc) n)
#pop-options

(*** Oracle-free guarded recursion: mufby ***)

(* Transfer core: [mufby v0 body] and [mu (delayed_body v0 body)] have the same
   observable behaviour once the [mu] oracle guesses [mufby]'s own output. So a
   triple for the [mu]-run transfers, step by step, to the [mufby]-run. *)
#push-options "--z3rlimit 100"
let mufby_transfer_aux
  (#input #output: Type)
  (v0: output)
  (body: S.sys (output & input) output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (is: E.stream input)
  (orc: E.stream (SB.option_type_sem (S.mufby v0 body).oracle))
  (n: nat)
  : Lemma
    (requires
      ES.causal2 q /\
      triple p (S.mu (S.delayed_body v0 body)) q /\
      ES.sofar (p is) n /\
      ES.sofar
        (S.stream_of_assumptions (S.mufby v0 body).raw
          (S.with_oracle (S.mufby v0 body) is orc)) n)
    (ensures (
      let ios = S.with_oracle (S.mufby v0 body) is orc in
      ES.sofar (q is (S.stream_of_output (S.mufby v0 body).raw ios)) n /\
      ES.sofar (S.stream_of_obligations (S.mufby v0 body).raw ios) n))
  =
  let mufby_sys = S.mufby v0 body in
  let mu_sys    = S.mu (S.delayed_body v0 body) in
  let t1        = (S.delayed_body v0 body).raw in
  let ios_mufby = S.with_oracle mufby_sys is orc in
  let os_mufby  = S.stream_of_output mufby_sys.raw ios_mufby in
  let orc_mu : E.stream (SB.option_type_sem mu_sys.oracle) =
    fun k -> SB.type_join_tup #(Some output) #body.oracle (os_mufby k) (orc k) in
  let ios_mu : S.io_stream input (SB.type_join (Some output) body.oracle) =
    S.with_oracle mu_sys is orc_mu in
  let body_ios  = S.mu_body_ios ios_mu in
  let os_mu     = S.stream_of_output mu_sys.raw ios_mu in
  let dib       = S.delayed_body_ios v0 body.raw body_ios in
  let mib       = S.mufby_body_ios v0 body.raw ios_mufby in

  (* Oracle reductions: the [mu] guess is [mufby]'s output, and the remaining
     oracle component is [orc]. *)
  introduce forall (k: nat). S.mu_guess ios_mu k == os_mufby k
    with S.lemma_type_join_fst_tup #(Some output) #body.oracle (os_mufby k) (orc k);
  introduce forall (k: nat).
      SB.type_join_snd #(Some output) #body.oracle (snd (ios_mu k)) == orc k
    with S.lemma_type_join_snd_tup #(Some output) #body.oracle (os_mufby k) (orc k);

  (* System [mu] laws, [delayed_body] and [mufby] unfolds, at every step. *)
  Classical.forall_intro (S.lemma_stream_of_output_system_mu t1 ios_mu);
  Classical.forall_intro (S.lemma_stream_of_obligations_system_mu t1 ios_mu);
  Classical.forall_intro (S.lemma_stream_of_assumptions_system_mu t1 ios_mu);
  Classical.forall_intro (S.lemma_system_delayed_body v0 body.raw body_ios);
  Classical.forall_intro (S.lemma_system_mufby v0 body.raw ios_mufby);

  (* The io-stream [delayed_body] feeds [body] under the [mu] run equals the one
     [mufby] feeds [body]: both are the [v0 fby os_mufby] feedback with [is] and
     [orc]. Congruence then equates their body runs. *)
  assert (forall (k: nat). dib k == mib k);
  introduce forall (k: nat).
      S.stream_of_output body.raw dib k == S.stream_of_output body.raw mib k
    with S.lemma_stream_of_output_congruence body.raw dib mib k;
  introduce forall (k: nat).
      S.stream_of_assumptions body.raw dib k == S.stream_of_assumptions body.raw mib k
    with S.lemma_stream_of_assumptions_congruence body.raw dib mib k;
  introduce forall (k: nat).
      S.stream_of_obligations body.raw dib k == S.stream_of_obligations body.raw mib k
    with S.lemma_stream_of_obligations_congruence body.raw dib mib k;

  (* Consequently the two systems have equal output / assumptions / obligations. *)
  assert (forall (k: nat). os_mu k == os_mufby k);
  assert (forall (k: nat).
    S.stream_of_assumptions mu_sys.raw ios_mu k <==>
      S.stream_of_assumptions mufby_sys.raw ios_mufby k);
  assert (forall (k: nat).
    S.stream_of_obligations mu_sys.raw ios_mu k ==
      S.stream_of_obligations mufby_sys.raw ios_mufby k);

  (* [mufby]'s assumptions hold so far, hence [mu]'s do too; invoke the [mu]
     triple, then transport [Q] and the obligations back to [mufby]. *)
  assert (ES.sofar (S.stream_of_assumptions mu_sys.raw ios_mu) n);
  assert (ES.sofar (q is os_mu) n /\
          ES.sofar (S.stream_of_obligations mu_sys.raw ios_mu) n);
  ES.lemma_causal2_prefix q is is os_mu os_mufby n;
  assert (ES.sofar (q is os_mufby) n);
  assert (ES.sofar (S.stream_of_obligations mufby_sys.raw ios_mufby) n)

let mufby #input #output v0 body p q =
  mu p (S.delayed_body v0 body) q;
  Classical.forall_intro_3
    (fun is orc n -> Classical.move_requires (mufby_transfer_aux v0 body p q is orc) n)
#pop-options

(* [mufby_guard] is causal: the [later] appears only under [pre], so its value at
   [n] depends only on the [jxs] prefix up to [n]. *)
let lemma_mufby_guard_causal #input #output v0 p q =
  let g = mufby_guard v0 p q in
  let aux (jxs1 jxs2: E.stream (output & input)) (n: nat)
    : Lemma
      (requires (forall (k: nat). k <= n ==> jxs1 k == jxs2 k))
      (ensures g jxs1 n <==> g jxs2 n)
    =
    ES.lemma_causal_prefix p (source jxs1) (source jxs2) n;
    (if n > 0 then
      ES.lemma_causal2_prefix q (source jxs1) (source jxs2)
        (ES.later (feedback jxs1)) (ES.later (feedback jxs2)) (n - 1))
  in
  Classical.forall_intro_3 (fun jxs1 jxs2 n -> Classical.move_requires (aux jxs1 jxs2) n)

(* Core of [mufby_step]: from a triple about [body] with the [mufby_guard]
   precondition, discharge [mu]'s premise for [delayed_body v0 body] step by
   step. The body is run on [delayed_body_ios] (its feedback delayed by
   [v0 fby -]); the guard's [later] cancels that [fby] so the [mufby_guard] on
   the delayed input matches [mu_body_pre]. *)
#push-options "--z3rlimit 100"
let mufby_step_aux
  (#input #output: Type)
  (v0: output)
  (body: S.sys (output & input) output)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (ixs: E.stream (output & input))
  (orc: E.stream (SB.option_type_sem (S.delayed_body v0 body).oracle))
  (n: nat)
  : Lemma
    (requires
      ES.causal p /\ ES.causal2 q /\
      triple (mufby_guard v0 p q) body (mu_body_post q) /\
      ES.sofar (mu_body_pre p q ixs) n /\
      ES.sofar
        (S.stream_of_assumptions (S.delayed_body v0 body).raw
          (S.with_oracle (S.delayed_body v0 body) ixs orc)) n)
    (ensures (
      let ios = S.with_oracle (S.delayed_body v0 body) ixs orc in
      let os  = S.stream_of_output (S.delayed_body v0 body).raw ios in
      ES.sofar (mu_body_post q ixs os) n /\
      ES.sofar (S.stream_of_obligations (S.delayed_body v0 body).raw ios) n))
  =
  let db    = S.delayed_body v0 body in
  let ios   = S.with_oracle db ixs orc in
  let dios  = S.delayed_body_ios v0 body.raw ios in
  (* Body input for the triple: the delayed-feedback io-stream, viewed as a
     plain body input stream. *)
  let jxs : E.stream (output & input) = fun k -> fst (dios k) in
  let ios_b = S.with_oracle body jxs orc in
  let os_b  = S.stream_of_output body.raw ios_b in
  let os    = S.stream_of_output db.raw ios in

  (* [delayed_body] unfold, and [dios] equals the body io-stream [ios_b]. *)
  Classical.forall_intro (S.lemma_system_delayed_body v0 body.raw ios);
  assert (forall (k: nat). dios k == ios_b k);
  introduce forall (k: nat). S.stream_of_output body.raw dios k == os_b k
    with S.lemma_stream_of_output_congruence body.raw dios ios_b k;
  introduce forall (k: nat).
      S.stream_of_assumptions body.raw dios k == S.stream_of_assumptions body.raw ios_b k
    with S.lemma_stream_of_assumptions_congruence body.raw dios ios_b k;
  introduce forall (k: nat).
      S.stream_of_obligations body.raw dios k == S.stream_of_obligations body.raw ios_b k
    with S.lemma_stream_of_obligations_congruence body.raw dios ios_b k;

  (* [jxs]'s feedback/source relate to [ixs]: [later] cancels the [fby] delay. *)
  assert (forall (m: nat). ES.later (feedback jxs) m == feedback ixs m);
  assert (forall (k: nat). source jxs k == source ixs k);
  assert (feedback jxs 0 == v0);

  (* Guard implication: [mu_body_pre p q ixs] ==> [mufby_guard v0 p q jxs]. *)
  ES.lemma_causal_prefix p (source jxs) (source ixs) n;
  (if n > 0 then
    ES.lemma_causal2_prefix q (source jxs) (source ixs)
      (ES.later (feedback jxs)) (feedback ixs) (n - 1));
  ES.sofar_index (mu_body_pre p q ixs) n;
  assert (ES.sofar (mufby_guard v0 p q jxs) n);

  (* Body assumptions hold on [ios_b]; the body triple gives the post + obl. *)
  assert (ES.sofar (S.stream_of_assumptions body.raw ios_b) n);
  assert (ES.sofar (mu_body_post q jxs os_b) n);
  assert (ES.sofar (S.stream_of_obligations body.raw ios_b) n);

  (* Transport the postcondition and obligations back to [ixs]/[os]. *)
  ES.lemma_causal2_prefix q (source jxs) (source ixs) os_b os n;
  assert (ES.sofar (mu_body_post q ixs os) n);
  assert (ES.sofar (S.stream_of_obligations db.raw ios) n)

let mufby_step #input #output v0 body p q =
  let aux
    (ixs: E.stream (output & input))
    (orc: E.stream (SB.option_type_sem (S.delayed_body v0 body).oracle))
    (n: nat)
    : Lemma
      (ensures (
        let ios = S.with_oracle (S.delayed_body v0 body) ixs orc in
        let os  = S.stream_of_output (S.delayed_body v0 body).raw ios in
        ES.sofar (mu_body_pre p q ixs) n ==>
        ES.sofar (S.stream_of_assumptions (S.delayed_body v0 body).raw ios) n ==>
        (ES.sofar (mu_body_post q ixs os) n /\
         ES.sofar (S.stream_of_obligations (S.delayed_body v0 body).raw ios) n)))
    =
    Classical.move_requires (mufby_step_aux v0 body p q ixs orc) n
  in
  Classical.forall_intro_3 aux;
  mufby v0 body p q
#pop-options
