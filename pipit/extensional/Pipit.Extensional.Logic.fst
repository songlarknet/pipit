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

(* Prefix transport for a causal predicate: pointwise-equal prefixes give the
   same truth at every step of the prefix. *)
let lemma_causal_prefix
  (#a: Type)
  (p: E.stream a -> E.stream prop)
  (xs1 xs2: E.stream a)
  (n: nat)
  : Lemma
    (requires
      causal p /\
      (forall (k: nat). k <= n ==> xs1 k == xs2 k))
    (ensures forall (k: nat). k <= n ==> (p xs1 k <==> p xs2 k))
  =
  let aux (k: nat) : Lemma (requires k <= n) (ensures p xs1 k <==> p xs2 k) = () in
  Classical.forall_intro (Classical.move_requires aux)

(* Prefix transport for a causal postcondition: pointwise-equal input and output
   prefixes give the same postcondition truth at every step of the prefix. *)
let lemma_causal_post_prefix
  (#input #output: Type)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (is1 is2: E.stream input)
  (os1 os2: E.stream output)
  (n: nat)
  : Lemma
    (requires
      causal_post q /\
      (forall (k: nat). k <= n ==> is1 k == is2 k) /\
      (forall (k: nat). k <= n ==> os1 k == os2 k))
    (ensures forall (k: nat). k <= n ==> (q is1 os1 k <==> q is2 os2 k))
  =
  let aux (k: nat) : Lemma (requires k <= n) (ensures q is1 os1 k <==> q is2 os2 k) = () in
  Classical.forall_intro (Classical.move_requires aux)

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
      causal p /\
      causal_post q /\
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
  lemma_causal_prefix p (source is') is n;
  lemma_causal_post_prefix q (source is') is (feedback is') os_mu n;
  lemma_causal_post_prefix q (source is') is os' os_mu n;

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
