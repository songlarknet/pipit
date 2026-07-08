(* Extensional program logic over transition systems.

   The judgement [triple P t Q] reads: for every input stream [is] and every
   oracle stream that keeps the system's rely-assumptions satisfied so far, if
   the precondition stream [P is] holds so far, then both the postcondition
   stream [Q is os] and the system's own obligations hold so far — where [os]
   is the observable output stream produced by [t].

   Preconditions and postconditions are [stream prop] transformers, and the
   judgement is closed under prefixes via [sofar], which is what makes the
   guarded recursion rule statable.
*)
module Pipit.Extensional.Logic

module E   = Pipit.Extensional.Base
module ES  = Pipit.Extensional.Stream
module EPS = Pipit.Extensional.PStream
module S   = Pipit.Extensional.System

module Classical = FStar.Classical

open Pipit.System.Base
open Pipit.Extensional.System

(* Extensional triple judgement.

   Universally quantifies the oracle stream, restricting to runs where the
   rely-assumptions have held so far. The consequent bundles the caller's
   postcondition [Q] with the system's own obligations. *)
let triple
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (t: sys input output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : prop
  =
  forall (is: E.stream input)
         (orc: E.stream (option_type_sem t.oracle))
         (n: nat).
    let ios = with_oracle t is orc in
    let os  = S.stream_of_output t.raw ios in
    ES.sofar (p is) n ==>
    ES.sofar (S.stream_of_assumptions t.raw ios) n ==>
    (ES.sofar (q is os) n /\
     ES.sofar (S.stream_of_obligations t.raw ios) n)

(*** Guarded recursion ***)

(* Projections of a [mu]-body input stream: the source input and the recursive
   feedback (the candidate output being defined). *)
let source
  (#input #output: Type)
  (ixs: E.stream (output & input))
  : E.stream input
  =
  fun n -> snd (ixs n)

let feedback
  (#input #output: Type)
  (ixs: E.stream (output & input))
  : E.stream output
  =
  fun n -> fst (ixs n)

(* Assemble a [mu]-body input stream from a feedback stream and a source input
   stream. Kept transparent so [source] reduces pointwise to the inputs. *)
let mu_body_input
  (#input #output: Type)
  (fb: E.stream output)
  (is: E.stream input)
  : E.stream (output & input)
  =
  fun n -> (fb n, is n)

(* A stream predicate is causal (prefix-determined / a safety property) when its
   truth at step [n] depends only on the stream prefix up to [n]. *)
let causal
  (#a: Type)
  (p: E.stream a -> E.stream prop)
  : prop
  =
  forall (xs1 xs2: E.stream a) (n: nat).
    (forall (k: nat). k <= n ==> xs1 k == xs2 k) ==>
    (p xs1 n <==> p xs2 n)

(* The postcondition analogue of [causal] over an input and an output stream.
   NB: this is deliberately the explicit two-stream form rather than
   [causal (fun ios -> q (map fst ios) (map snd ios))]. The combined form is
   strictly weaker to use: recovering [q is1 os1 n <==> q is2 os2 n] from it
   would require rewriting [map fst (join is1 os1)] back to [is1], i.e.
   plain-arrow eta/functional extensionality, which F* does not provide. *)
let causal_post
  (#input #output: Type)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : prop
  =
  forall (is1 is2: E.stream input) (os1 os2: E.stream output) (n: nat).
    (forall (k: nat). k <= n ==> is1 k == is2 k) ==>
    (forall (k: nat). k <= n ==> os1 k == os2 k) ==>
    (q is1 os1 n <==> q is2 os2 n)

(* Recursive knot as a system combinator lives in [System] as [System.mu]. *)

(* Guarded body precondition: [P] on the source input, and [pre (Q x)] on the
   recursive feedback [x]. *)
let mu_body_pre
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (ixs: E.stream (output & input))
  : E.stream prop
  =
  fun n -> p (source ixs) n /\ ES.pre (q (source ixs) (feedback ixs)) n

(* Body postcondition: [Q] on the source input and the body output. *)
let mu_body_post
  (#input #output: Type)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (ixs: E.stream (output & input))
  (os: E.stream output)
  : E.stream prop
  =
  fun n -> q (source ixs) os n

(* Guarded recursion rule:

     Q causal
     { fun ixs n -> P (source ixs) n /\ pre (Q (source ixs) (feedback ixs)) n }
       body
     { fun ixs os n -> Q (source ixs) os n }
     -------------------------------------------------------------------------
     { P } mu body { Q }
*)

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
let rec triple_mu_aux
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (body: sys (output & input) output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  (is: E.stream input)
  (orc: E.stream (option_type_sem (mu body).oracle))
  (n: nat)
  : Lemma
    (requires
      causal p /\
      causal_post q /\
      triple (mu_body_pre p q) body (mu_body_post q) /\
      ES.sofar (p is) n /\
      ES.sofar (S.stream_of_assumptions (mu body).raw (with_oracle (mu body) is orc)) n)
    (ensures (
      let ios_mu = with_oracle (mu body) is orc in
      ES.sofar (q is (S.stream_of_output (mu body).raw ios_mu)) n /\
      ES.sofar (S.stream_of_obligations (mu body).raw ios_mu) n))
    (decreases n)
  =
  let t1       = body.raw in
  let ios_mu   = with_oracle (mu body) is orc in
  let body_ios = S.mu_body_ios ios_mu in
  let os_mu    = S.stream_of_output (mu body).raw ios_mu in
  let fb : E.stream output = fun k -> S.mu_guess ios_mu k in
  let is' : E.stream (output & input) = mu_body_input fb is in
  let orc' : E.stream (option_type_sem body.oracle) =
    fun k -> type_join_snd #(Some output) #body.oracle (snd (ios_mu k)) in
  let ios'     = with_oracle body is' orc' in
  let os'      = S.stream_of_output body.raw ios' in

  (* [mu body]'s underlying system is [system_mu] of the body's system. *)
  assert ((mu body).raw == system_mu t1);

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
    ES.sofar_weaken (S.stream_of_assumptions (mu body).raw ios_mu) n (n - 1);
    triple_mu_aux p body q is orc (n - 1)
  end);

  (* Expose the hypotheses (and, when n>0, the IH) at every step. *)
  ES.sofar_index (p is) n;
  ES.sofar_index (S.stream_of_assumptions (mu body).raw ios_mu) n;
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
  assert (ES.sofar (S.stream_of_obligations (mu body).raw ios_mu) n)

let triple_mu
  (#input #output: Type)
  (p: E.stream input -> E.stream prop)
  (body: sys (output & input) output)
  (q: E.stream input -> E.stream output -> E.stream prop)
  : Lemma
    (requires
      causal p /\
      causal_post q /\
      triple (mu_body_pre p q) body (mu_body_post q))
    (ensures
      triple p (mu body) q)
  =
  let aux
    (is: E.stream input)
    (orc: E.stream (option_type_sem (mu body).oracle))
    (n: nat)
    : Lemma
      (ensures (
        let ios = with_oracle (mu body) is orc in
        ES.sofar (p is) n ==>
        ES.sofar (S.stream_of_assumptions (mu body).raw ios) n ==>
        (ES.sofar (q is (S.stream_of_output (mu body).raw ios)) n /\
         ES.sofar (S.stream_of_obligations (mu body).raw ios) n)))
    =
    Classical.move_requires (triple_mu_aux p body q is orc) n
  in
  Classical.forall_intro_3 aux
#pop-options
