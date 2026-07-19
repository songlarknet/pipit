(* Pipit.Source.Stream -- a Sugar-style source layer over the stream terms. A
   `stream a` is a reducible builder that, given a fresh-name counter, emits a
   width-1 `tterm` and the next counter; `a` is phantom. Design notes and
   rationale: see Pipit.Source.Stream.md. *)
module Pipit.Source.Stream

module PEB = Pipit.Exp.Base

type stream (a: PEB.typ) = nat -> PEB.tterm & nat

let fresh (a: PEB.typ) (n: nat): PEB.svar & nat =
  ({ PEB.svname = n; svty = a }, n + 1)

(* Reduce a width-1 stream term to an `sterm` operand plus a wrapper installing
   any binding the reduction needed (meta-unwrap: `TTuple [e]` inlines to `e`). *)
let atomize (a: PEB.typ) (t: PEB.tterm) (n: nat)
: PEB.sterm & (PEB.tterm -> PEB.tterm) & nat =
  match t with
  | PEB.TTuple [e] -> (e, (fun body -> body), n)
  | _ ->
    let (x, n) = fresh a n in
    (PEB.SVar x, (fun body -> PEB.TLet [a] t (PEB.close_rec_t 0 x body)), n)

let fvar (#a: PEB.typ) (x: PEB.svar): stream a =
  fun n -> (PEB.TTuple [PEB.SVar x], n)

let const (#a: PEB.typ) (v: PEB.pterm): stream a =
  fun n -> (PEB.TTuple [PEB.SPure v], n)

let fby (#a: PEB.typ) (v: PEB.pterm) (s: stream a): stream a =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PEB.TTuple [PEB.SFby v e]), n)

let liftP1 (#a #b: PEB.typ) (p: PEB.pterm) (s: stream a): stream b =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PEB.TTuple [PEB.SPureApp p [e]]), n)

let liftP2 (#a #b #c: PEB.typ)
    (p: PEB.pterm) (s1: stream a) (s2: stream b): stream c =
  fun n ->
    let (t1, n)     = s1 n in
    let (e1, w1, n) = atomize a t1 n in
    let (t2, n)     = s2 n in
    let (e2, w2, n) = atomize b t2 n in
    (w1 (w2 (PEB.TTuple [PEB.SPureApp p [e1; e2]])), n)

(* Non-recursive shared binding: `f` is applied to one fresh variable, so the
   rhs is emitted once (no HOAS duplication). *)
let let' (#a #b: PEB.typ)
    (e: stream a) (f: stream a -> stream b): stream b =
  fun n ->
    let (ev, n)    = e n in
    let (x, n)     = fresh a n in
    let (bodyv, n) = f (fvar x) n in
    (PEB.TLet [a] ev (PEB.close_rec_t 0 x bodyv), n)

(* Single-stream recursion `x = f x`: the n = 1 case of the core's `TRec`. *)
let mu (#a: PEB.typ) (f: stream a -> stream a): stream a =
  fun n ->
    let (x, n)     = fresh a n in
    let (bodyv, n) = f (fvar x) n in
    (PEB.TRec [a] (PEB.close_rec_t 0 x bodyv), n)

let letrec1 (#a #b: PEB.typ)
    (f: stream a -> stream a) (cont: stream a -> stream b): stream b =
  let' (mu f) cont

(* Multi-output node instantiation (2 inputs, 2 outputs). Node arguments MUST be
   atoms (counter-stable `fvar` / `const`); bind non-atomic arguments with `let'`
   first. See Pipit.Source.Stream.md. *)
let node22 (#i1 #i2 #o1 #o2: PEB.typ)
    (head: string) (s1: stream i1) (s2: stream i2)
    : stream o1 & stream o2 =
  let build (i: nat) (n: nat): PEB.tterm =
    let (t1, n)     = s1 n in
    let (e1, w1, n) = atomize i1 t1 n in
    let (t2, n)     = s2 n in
    let (e2, w2, n) = atomize i2 t2 n in
    w1 (w2 (PEB.TLet [o1; o2] (PEB.TStreamApp head [e1; e2]) (PEB.TTuple [PEB.SBVar i])))
  in
  ( (fun n -> (build 0 n, n))
  , (fun n -> (build 1 n, n)) )

let exp_of_stream (#a: PEB.typ) (s: stream a): PEB.tterm =
  fst (s 0)
