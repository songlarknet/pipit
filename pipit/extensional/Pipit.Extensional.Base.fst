(* Extensional/observational foundations for stream and system semantics.
   This package hosts stream-indexed views and rewrite-facing abstractions
   that are independent of system internal state representation. *)
module Pipit.Extensional.Base

(* Streams as discrete signals indexed by natural-number steps. *)
type stream (a: Type) = nat -> a

(* Per-step proof-carrying observation: value plus assumption/obligation facts. *)
noeq
type pobs (a: Type) = {
   pv: a;
   pasm: prop;
   pobl: prop;
}

(* A stream of proof-carrying observations. *)
type pstream (a: Type) = stream (pobs a)
