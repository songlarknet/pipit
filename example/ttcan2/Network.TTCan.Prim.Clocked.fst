(* Helpers for encoding clocked streams *)
module Network.TTCan.Prim.Clocked
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

type t (a: eqtype) = option a

instance has_stream_t (a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (t a) = {
  ty_id = `%t :: (PSSB.ty_id #a);
  val_default = None;
}

let get_clock (#a: eqtype) (v: t a): bool = Some? v
let get_value (#a: eqtype) {| PSSB.has_stream a |} (v: t a): a =
  match v with
  | Some v -> v
  | None -> PSSB.val_default

let fold (#a #b: eqtype)
  (zero: b)
  (kons: a -> b)
  (clck: t a)
       : b =
  match clck with
  | Some v -> kons v
  | None -> zero

let get_or_else (#a: eqtype) (dflt: a) (clck: t a): a =
  match clck with
  | Some v -> v
  | None -> dflt

let map (#a #b: eqtype) (fn: a -> b) (clck: t a): t b = FStar.Option.mapTot fn clck

let current_or_else (#a: eqtype) {| PSSB.has_stream a |}
  (dflt: a) (clck: stream (t a)): stream a =
  rec' (fun acc ->
    get_or_else (dflt `fby` acc) clck)

let or_else (#a: eqtype) (u v: t a): t a =
  match u with
  | Some _ -> u
  | None   -> v
