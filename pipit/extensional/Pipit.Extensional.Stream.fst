(* Basic stream combinators used by extensional system lemmas. *)
module Pipit.Extensional.Stream

module E = Pipit.Extensional.Base
module Classical = FStar.Classical

(* Constant stream. *)
let const (#a: Type) (x: a): E.stream a =
  fun _ -> x

(* Map a pure function pointwise over a stream. *)
let map (#a #b: Type) (f: a -> b) (xs: E.stream a): E.stream b =
  fun n -> f (xs n)

(* Pointwise extensional equality on streams. *)
let eq (#a: Type) (x y: E.stream a): prop =
  forall (n: nat). x n == y n

(* A pointwise predicate holding at every step of a stream. *)
let holds (#a: Type) (p: a -> prop) (s: E.stream a): prop =
  forall (n: nat). p (s n)

(* Transport a pointwise stream predicate along extensional stream equality. *)
let holds_of_eq
  (#a: Type)
  (p: a -> prop)
  (s1 s2: E.stream a)
  : Lemma
    (requires eq s1 s2 /\ holds p s1)
    (ensures holds p s2)
  =
  introduce forall (n: nat). p (s2 n)
  with ( assert (s1 n == s2 n) )

(* Prefix closure of a temporal predicate stream: [sofar ps n] holds iff [ps]
   holds at every step up to and including [n]. *)
let sofar (ps: E.stream prop): E.stream prop =
  fun n -> forall (n': nat). n' <= n ==> ps n'

(* [sofar ps n] exposes [ps] at every step up to [n]. *)
let sofar_index (ps: E.stream prop) (n: nat)
  : Lemma (requires sofar ps n) (ensures forall (k: nat). k <= n ==> ps k)
  =
  ()

(* [sofar] is antitone in the horizon: holding to [n] implies holding to any
   earlier [m]. *)
let sofar_weaken (ps: E.stream prop) (n m: nat)
  : Lemma (requires sofar ps n /\ m <= n) (ensures sofar ps m)
  =
  ()

(* One-step delay on a temporal predicate stream: [pre ps 0] is trivially true,
   and [pre ps n] is [ps (n-1)] afterwards. *)
let pre (ps: E.stream prop): E.stream prop =
  fun n ->
    match n with
    | 0 -> True
    | _ -> ps (n - 1)

(* [fby v0 xs]: emit [v0] at step 0, then the previous value of [xs]. The value
   analogue of [pre]. *)
let fby (#a: Type) (v0: a) (xs: E.stream a): E.stream a =
  fun n ->
    match n with
    | 0 -> v0
    | _ -> xs (n - 1)

(*** Causality (prefix-determinism) ***)

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

(* Two-argument analogue of [causal]: truth at step [n] depends only on the two
   input prefixes up to [n].

   NB: this is deliberately the explicit two-stream form rather than
   [causal (fun xys -> q (map fst xys) (map snd xys))]. The combined form is
   strictly weaker to use: recovering [q xs1 ys1 n <==> q xs2 ys2 n] from it
   would require rewriting [map fst (join xs1 ys1)] back to [xs1], i.e.
   plain-arrow eta/functional extensionality, which F* does not provide. *)
let causal2
  (#a #b: Type)
  (q: E.stream a -> E.stream b -> E.stream prop)
  : prop
  =
  forall (xs1 xs2: E.stream a) (ys1 ys2: E.stream b) (n: nat).
    (forall (k: nat). k <= n ==> xs1 k == xs2 k) ==>
    (forall (k: nat). k <= n ==> ys1 k == ys2 k) ==>
    (q xs1 ys1 n <==> q xs2 ys2 n)

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

(* Prefix transport for a [causal2] predicate. *)
let lemma_causal2_prefix
  (#a #b: Type)
  (q: E.stream a -> E.stream b -> E.stream prop)
  (xs1 xs2: E.stream a)
  (ys1 ys2: E.stream b)
  (n: nat)
  : Lemma
    (requires
      causal2 q /\
      (forall (k: nat). k <= n ==> xs1 k == xs2 k) /\
      (forall (k: nat). k <= n ==> ys1 k == ys2 k))
    (ensures forall (k: nat). k <= n ==> (q xs1 ys1 k <==> q xs2 ys2 k))
  =
  let aux (k: nat) : Lemma (requires k <= n) (ensures q xs1 ys1 k <==> q xs2 ys2 k) = () in
  Classical.forall_intro (Classical.move_requires aux)
