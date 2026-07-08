(* Basic stream combinators used by extensional system lemmas. *)
module Pipit.Extensional.Stream

module E = Pipit.Extensional.Base

(* Constant stream. *)
let const (#a: Type) (x: a): E.stream a =
  fun _ -> x

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
