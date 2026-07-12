(* Combinators for proof-carrying streams. *)
module Pipit.Extensional.PStream

module E = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream

(* Extensional equivalence on proof-carrying streams.
   All components are definitionally equal at each step. *)
let eq
  (#a: Type)
  (x y: E.pstream a)
  : prop
  =
  forall (n: nat).
      (x n).pv == (y n).pv /\
    (x n).pasm == (y n).pasm /\
    (x n).pobl == (y n).pobl

(* Project the value stream. *)
let values
  (#a: Type)
  (ps: E.pstream a)
  : E.stream a
  =
  fun n -> (ps n).pv

(* Project the assumptions stream. *)
let assumptions
  (#a: Type)
  (ps: E.pstream a)
  : E.stream prop
  =
  fun n -> (ps n).pasm

(* Project the obligations stream. *)
let obligations
  (#a: Type)
  (ps: E.pstream a)
  : E.stream prop
  =
  fun n -> (ps n).pobl

(* Build a proof-carrying stream from component streams. *)
let mk
  (#a: Type)
  (vals: E.stream a)
  (asms: E.stream prop)
  (obls: E.stream prop)
  : E.pstream a
  =
  fun n -> {
    pv = vals n;
    pasm = asms n;
    pobl = obls n;
  }

(* Constant proof-carrying stream. *)
let const
  (#a: Type)
  (v: a)
  (asm: prop)
  (obl: prop)
  : E.pstream a
  =
  fun _ -> {
    pv = v;
    pasm = asm;
    pobl = obl;
  }

(* pstream extensional equality implies value-stream equality. *)
let values_eq_of_eq
  (#a: Type)
  (x y: E.pstream a)
  : Lemma
    (requires eq x y)
    (ensures ES.eq (values x) (values y))
  =
  introduce forall (n: nat).
    values x n == values y n
  with (
    assert ((x n).pv == (y n).pv)
  )

(* pstream extensional equality implies assumptions-stream equality. *)
let assumptions_eq_of_eq
  (#a: Type)
  (x y: E.pstream a)
  : Lemma
    (requires eq x y)
    (ensures ES.eq (assumptions x) (assumptions y))
  =
  introduce forall (n: nat).
    assumptions x n == assumptions y n
  with (
    assert ((x n).pasm == (y n).pasm)
  )

(* pstream extensional equality implies obligations-stream equality. *)
let obligations_eq_of_eq
  (#a: Type)
  (x y: E.pstream a)
  : Lemma
    (requires eq x y)
    (ensures ES.eq (obligations x) (obligations y))
  =
  introduce forall (n: nat).
    obligations x n == obligations y n
  with (
    assert ((x n).pobl == (y n).pobl)
  )
