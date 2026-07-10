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

(* Decode a prop-valued postcondition system (over paired input & output) into a
   two-stream predicate. *)
unfold
let spred2
  (#input #output: Type)
  (q: dsys (input & output) prop)
  : E.stream input -> E.stream output -> E.stream prop
  =
  fun is os -> outputs_det q (fun n -> (is n, os n))

(* System-valued triple, defined by decoding the spec systems into the stream
   [Logic.triple]. *)
let triple
  (#input #output: Type)
  (pre: dsys input prop)
  (t: S.sys input output)
  (post: dsys (input & output) prop)
  : prop
  =
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
         (S.with_oracle q (fun m -> (is1 m, os1 m)) (fun (_: nat) -> ()))
         (S.with_oracle q (fun m -> (is2 m, os2 m)) (fun (_: nat) -> ()))
         n

(*** Deterministic spec constructors ***)

(* Constant spec system. *)
let sconst (#input #output: Type) (v: output) : dsys input output =
  { oracle = None; state = None; raw = SB.system_const v }

(* The input itself as a spec system. *)
let svar (#a: Type) : dsys a a = S.id #a

(* Map a pure function over a spec system's output. *)
let smap
  (#input #a #b: Type)
  (f: a -> b)
  (p: dsys input a)
  : dsys input b
  =
  S.map f p
