(* A Sugar-style source layer over the core stream terms: a `stream ts` is a
   reducible builder emitting a width-|ts| `tterm` from a fresh-name counter.
   Design notes and rationale: see Pipit.Source.Stream.md. *)
module Pipit.Source.Stream

module PEB = Pipit.Exp.Base
module L   = FStar.List.Tot

(* ----- Builder and fresh names ------------------------------------------ *)

type stream (ts: list PEB.typ) = nat -> PEB.tterm & nat

let fresh (a: PEB.typ) (n: nat): PEB.svar & nat =
  ({ PEB.svname = n; svty = a }, n + 1)

let rec fresh_vars (ts: list PEB.typ) (n: nat): list PEB.svar & nat =
  match ts with
  | []      -> ([], n)
  | a :: tl -> let (x, n)  = fresh a n in
               let (xs, n) = fresh_vars tl n in
               (x :: xs, n)

let rec close_vars (k: nat) (xs: list PEB.svar) (body: PEB.tterm): Tot PEB.tterm (decreases xs) =
  match xs with
  | []      -> body
  | x :: tl -> PEB.close_rec_t k x (close_vars (k + 1) tl body)

(* ----- Meta-unwrap ------------------------------------------------------ *)

let atomize (a: PEB.typ) (t: PEB.tterm) (n: nat)
: PEB.sterm & (PEB.tterm -> PEB.tterm) & nat =
  match t with
  | PEB.TTuple [e] -> (e, (fun body -> body), n)
  | _ ->
    let (x, n) = fresh a n in
    (PEB.SVar x, (fun body -> PEB.TLet [a] t (PEB.close_rec_t 0 x body)), n)

let components (ts: list PEB.typ) (t: PEB.tterm) (n: nat)
: list PEB.sterm & (PEB.tterm -> PEB.tterm) & nat =
  match t with
  | PEB.TTuple es -> (es, (fun body -> body), n)
  | _ ->
    let (xs, n) = fresh_vars ts n in
    (L.map (fun (x: PEB.svar) -> PEB.SVar x) xs,
     (fun body -> PEB.TLet ts t (close_vars 0 xs body)),
     n)

(* ----- Pointwise -------------------------------------------------------- *)

let fvar (#a: PEB.typ) (x: PEB.svar): stream [a] =
  fun n -> (PEB.TTuple [PEB.SVar x], n)

let const (#a: PEB.typ) (v: PEB.pterm): stream [a] =
  fun n -> (PEB.TTuple [PEB.SPure v], n)

let fby (#a: PEB.typ) (v: PEB.pterm) (s: stream [a]): stream [a] =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PEB.TTuple [PEB.SFby v e]), n)

let liftP (#args: list PEB.typ) (#result: PEB.typ)
    (p: PEB.pterm) (s: stream args): stream [result] =
  fun n ->
    let (t, n)     = s n in
    let (es, w, n) = components args t n in
    (w (PEB.TTuple [PEB.SPureApp p es]), n)

(* ----- Tupling ---------------------------------------------------------- *)

let zips (#xs #ys: list PEB.typ) (x: stream xs) (y: stream ys): stream (L.append xs ys) =
  fun n ->
    let (tx, n)      = x n in
    let (exs, wx, n) = components xs tx n in
    let (ty, n)      = y n in
    let (eys, wy, n) = components ys ty n in
    (wx (wy (PEB.TTuple (L.append exs eys))), n)

let unzips (#xs #ys: list PEB.typ) (s: stream (L.append xs ys)): stream xs & stream ys =
  let k = L.length xs in
  ( (fun n ->
      let (t, n)     = s n in
      let (es, w, n) = components (L.append xs ys) t n in
      (w (PEB.TTuple (fst (L.splitAt k es))), n))
  , (fun n ->
      let (t, n)     = s n in
      let (es, w, n) = components (L.append xs ys) t n in
      (w (PEB.TTuple (snd (L.splitAt k es))), n)) )

let zip2 (#a: PEB.typ) (#b: list PEB.typ)
    (x: stream [a]) (y: stream b): stream (a :: b) =
  zips x y

let zip3 (#a #b: PEB.typ) (#c: list PEB.typ)
    (x: stream [a]) (y: stream [b]) (z: stream c): stream (a :: b :: c) =
  zips x (zips y z)

let unzip2 (#a: PEB.typ) (#b: list PEB.typ)
    (s: stream (a :: b)): stream [a] & stream b =
  unzips #[a] #b s

let unzip3 (#a #b: PEB.typ) (#c: list PEB.typ)
    (s: stream (a :: b :: c)): stream [a] & stream [b] & stream c =
  let (x, yz) = unzips #[a] #(b :: c) s in
  let (y, z)  = unzips #[b] #c yz in
  (x, y, z)

(* ----- Binding and recursion -------------------------------------------- *)

let let' (#a #b: list PEB.typ)
    (e: stream a) (f: stream a -> stream b): stream b =
  fun n ->
    let (ev, n)    = e n in
    let (xs, n)    = fresh_vars a n in
    let sref: stream a = (fun m -> (PEB.TTuple (L.map (fun (x: PEB.svar) -> PEB.SVar x) xs), m)) in
    let (bodyv, n) = f sref n in
    (PEB.TLet a ev (close_vars 0 xs bodyv), n)

let mu (#a: list PEB.typ) (f: stream a -> stream a): stream a =
  fun n ->
    let (xs, n)    = fresh_vars a n in
    let sref: stream a = (fun m -> (PEB.TTuple (L.map (fun (x: PEB.svar) -> PEB.SVar x) xs), m)) in
    let (bodyv, n) = f sref n in
    (PEB.TRec a (close_vars 0 xs bodyv), n)

let letrec (#a #b: list PEB.typ)
    (f: stream a -> stream a) (cont: stream a -> stream b): stream b =
  let' (mu f) cont

(* ----- Nodes ------------------------------------------------------------ *)

let node (#args #results: list PEB.typ)
    (head: string) (s: stream args): stream results =
  fun n ->
    let (t, n)     = s n in
    let (es, w, n) = components args t n in
    (w (PEB.TStreamApp head es), n)

(* ----- Lowering --------------------------------------------------------- *)

let exp_of_stream (#a: list PEB.typ) (s: stream a): PEB.tterm =
  fst (s 0)
