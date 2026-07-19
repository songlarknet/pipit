(* Pipit.Source.Stream -- a Sugar-style source layer over the stream terms.

   A `stream a` is a *builder* for a stream term of (object-level) type `a`: a
   computation that, given a fresh-name counter, emits a (width-1) `tterm` and
   the next
   counter. The result-type tag `a: typ` is phantom -- it never appears in the
   emitted term except as the binder annotations `let'` / `mu` recover from it --
   but it disciplines how the combinators compose. A later `check`/`infer` pass
   reconciles the two worlds.

   The representation is a plain function, i.e. *reducible*: lowering / checking
   can `norm` a `stream` down to a concrete `tterm`. Free `SVar`s are allocated
   with a monotone counter and eliminated by the core's `close`, mirroring
   Pipit 1's Sugar layer (fresh-name monad + `close`).

   Still to land, gated on a core extension:
     - `letrec2` / mutual recursion needs an n-ary source combinator over `TRec`
       (the single-stream `mu` below is the n = 1 case);
     - a CSE / sharing-recovery pass to hoist the `TStreamApp` that `node22`
       duplicates across its two outputs into a single shared binding. *)
module Pipit.Source.Stream

module PEB = Pipit.Exp.Base

(* A builder for a stream term of type `a`. `a` is phantom (guides composition).
   A stream is represented as a (width-1) `tterm`; the pointwise combinators
   *meta-unwrap* a plain `TTuple [e]` back to the single `sterm` `e` (via
   `atomize`), so ordinary expressions stay flat and only genuine tuples (node
   outputs) pay a `TLet`. *)
type stream (a: PEB.typ) = nat -> PEB.tterm & nat

(* Allocate a fresh named variable of type `a`. *)
let fresh (a: PEB.typ) (n: nat): PEB.svar & nat =
  ({ PEB.svname = n; svty = a }, n + 1)

(* Reduce a width-1 stream term to an `sterm` operand, with a wrapper that
   installs any binding the reduction needed. Fast path (the *meta*-unwrap): a
   plain `TTuple [e]` is already the single `sterm` `e`, inlined with no wrapper
   and no fresh name. Otherwise -- a node output `TLet ..`, the one genuine tuple
   case -- bind it to a fresh variable, so the operand becomes a variable
   reference and the returned wrapper is the enclosing `TLet`. *)
let atomize (a: PEB.typ) (t: PEB.tterm) (n: nat)
: PEB.sterm & (PEB.tterm -> PEB.tterm) & nat =
  match t with
  | PEB.TTuple [e] -> (e, (fun body -> body), n)
  | _ ->
    let (x, n) = fresh a n in
    (PEB.SVar x, (fun body -> PEB.TLet [a] t (PEB.close_rec_t 0 x body)), n)

(* A stream that just refers to an already-allocated free variable. *)
let fvar (#a: PEB.typ) (x: PEB.svar): stream a =
  fun n -> (PEB.TTuple [PEB.SVar x], n)

(* A constant stream holding the pure value `v`. *)
let const (#a: PEB.typ) (v: PEB.pterm): stream a =
  fun n -> (PEB.TTuple [PEB.SPure v], n)

(* `v fby s`: `v` on the first instant, then the previous value of `s`. *)
let fby (#a: PEB.typ) (v: PEB.pterm) (s: stream a): stream a =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PEB.TTuple [PEB.SFby v e]), n)

(* Lift a unary primitive `p` (a `pterm` head) over a stream (`p s`). The result
   tag `b` and argument tag `a` are phantom; the primitive's typing is checked
   later by `infer` against the signature environment. *)
let liftP1 (#a #b: PEB.typ) (p: PEB.pterm) (s: stream a): stream b =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PEB.TTuple [PEB.SPureApp p [e]]), n)

(* Lift a binary primitive `p` over two streams (`p s1 s2`). *)
let liftP2 (#a #b #c: PEB.typ)
    (p: PEB.pterm) (s1: stream a) (s2: stream b): stream c =
  fun n ->
    let (t1, n)     = s1 n in
    let (e1, w1, n) = atomize a t1 n in
    let (t2, n)     = s2 n in
    let (e2, w2, n) = atomize b t2 n in
    (w1 (w2 (PEB.TTuple [PEB.SPureApp p [e1; e2]])), n)

(* Non-recursive shared binding. `f` is applied to a *single* fresh variable, so
   every use of the bound stream in `f` shares one `TLet` binder and `e` is
   emitted once (no HOAS duplication). A single-stream `let` is the n = 1 tuple
   let: bind the width-1 `rhs` and continue with the (width-1) body. *)
let let' (#a #b: PEB.typ)
    (e: stream a) (f: stream a -> stream b): stream b =
  fun n ->
    let (ev, n)    = e n in
    let (x, n)     = fresh a n in
    let (bodyv, n) = f (fvar x) n in
    (PEB.TLet [a] ev (PEB.close_rec_t 0 x bodyv), n)

(* Single-stream recursion: the fixpoint `x` with `x = f x`. Built as the n = 1
   case of the core's n-ary `TRec`: a one-member group whose (width-1) body is
   the recursive definition. *)
let mu (#a: PEB.typ) (f: stream a -> stream a): stream a =
  fun n ->
    let (x, n)     = fresh a n in
    let (bodyv, n) = f (fvar x) n in
    (PEB.TRec [a] (PEB.close_rec_t 0 x bodyv), n)

(* A recursive definition, shared into a continuation. *)
let letrec1 (#a #b: PEB.typ)
    (f: stream a -> stream a) (cont: stream a -> stream b): stream b =
  let' (mu f) cont

(* Multi-output node instantiation (representative fixed arity: 2 stream inputs,
   2 stream outputs), returning an F* tuple of output streams so the caller can
   `let (o1, o2) = node22 head s1 s2 in ...`. Each output is its own
   `TLet [o1; o2] (TStreamApp head [e1; e2]) (TTuple [SBVar i])` binding the
   *same* application; because a term is a tree (not a DAG), that application
   subterm is duplicated across the two outputs, and a later CSE / sharing-
   recovery pass hoists it into one binding.

   Node arguments MUST be atoms -- counter-stable references such as `fvar` /
   `const` that allocate no fresh names -- since they are re-emitted under each
   output; a non-atom would allocate divergent fresh names in the two copies
   and break both the sharing CSE recovers and the single-instantiation meaning.
   Bind non-atomic arguments with `let'` first. *)
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

(* Emit the underlying stream term, allocating fresh names from 0. *)
let exp_of_stream (#a: PEB.typ) (s: stream a): PEB.tterm =
  fst (s 0)
