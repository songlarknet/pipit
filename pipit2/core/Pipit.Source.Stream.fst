(* A Sugar-style source layer over the core stream terms: a `stream ts` is a
   reducible builder emitting a width-|ts| `tterm` from a fresh-name counter.
   Design notes and rationale: see Pipit.Source.Stream.md. *)
module Pipit.Source.Stream

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source
module L   = FStar.List.Tot

(* ----- Builder and fresh names ------------------------------------------ *)

type stream (ts: list PR.typ) = nat -> PES.tterm & nat

let fresh (a: PR.typ) (n: nat): PES.svar & nat =
  ({ PES.svname = n; svty = a }, n + 1)

let rec fresh_vars (ts: list PR.typ) (n: nat): list PES.svar & nat =
  match ts with
  | []      -> ([], n)
  | a :: tl -> let (x, n)  = fresh a n in
               let (xs, n) = fresh_vars tl n in
               (x :: xs, n)

let rec close_vars (k: nat) (xs: list PES.svar) (body: PES.tterm): Tot PES.tterm (decreases xs) =
  match xs with
  | []      -> body
  | x :: tl -> PES.close_rec_t k x (close_vars (k + 1) tl body)

(* ----- Meta-unwrap ------------------------------------------------------ *)

let atomize (a: PR.typ) (t: PES.tterm) (n: nat)
: PES.sterm & (PES.tterm -> PES.tterm) & nat =
  match t with
  | PES.TTuple [e] -> (e, (fun body -> body), n)
  | _ ->
    let (x, n) = fresh a n in
    (PES.SVar x, (fun body -> PES.TLet [a] t (PES.close_rec_t 0 x body)), n)

let components (ts: list PR.typ) (t: PES.tterm) (n: nat)
: list PES.sterm & (PES.tterm -> PES.tterm) & nat =
  match t with
  | PES.TTuple es -> (es, (fun body -> body), n)
  | _ ->
    let (xs, n) = fresh_vars ts n in
    (L.map (fun (x: PES.svar) -> PES.SVar x) xs,
     (fun body -> PES.TLet ts t (close_vars 0 xs body)),
     n)

(* ----- Pointwise -------------------------------------------------------- *)

let fvar (#a: PR.typ) (x: PES.svar): stream [a] =
  fun n -> (PES.TTuple [PES.SVar x], n)

let const (#a: PR.typ) (v: PP.pterm): stream [a] =
  fun n -> (PES.TTuple [PES.SPure v], n)

let fby (#a: PR.typ) (v: PP.pterm) (s: stream [a]): stream [a] =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PES.TTuple [PES.SFby v e]), n)

let liftP (#args: list PR.typ) (#result: PR.typ)
    (p: PR.prim) (s: stream args): stream [result] =
  fun n ->
    let (t, n)     = s n in
    let (es, w, n) = components args t n in
    (w (PES.TTuple [PES.SPureApp p es]), n)

(* ----- Tupling ---------------------------------------------------------- *)

let zips (#xs #ys: list PR.typ) (x: stream xs) (y: stream ys): stream (L.append xs ys) =
  fun n ->
    let (tx, n)      = x n in
    let (exs, wx, n) = components xs tx n in
    let (ty, n)      = y n in
    let (eys, wy, n) = components ys ty n in
    (wx (wy (PES.TTuple (L.append exs eys))), n)

let unzips (#xs #ys: list PR.typ) (s: stream (L.append xs ys)): stream xs & stream ys =
  let k = L.length xs in
  ( (fun n ->
      let (t, n)     = s n in
      let (es, w, n) = components (L.append xs ys) t n in
      (w (PES.TTuple (fst (L.splitAt k es))), n))
  , (fun n ->
      let (t, n)     = s n in
      let (es, w, n) = components (L.append xs ys) t n in
      (w (PES.TTuple (snd (L.splitAt k es))), n)) )

let zip2 (#a: PR.typ) (#b: list PR.typ)
    (x: stream [a]) (y: stream b): stream (a :: b) =
  zips x y

let zip3 (#a #b: PR.typ) (#c: list PR.typ)
    (x: stream [a]) (y: stream [b]) (z: stream c): stream (a :: b :: c) =
  zips x (zips y z)

let unzip2 (#a: PR.typ) (#b: list PR.typ)
    (s: stream (a :: b)): stream [a] & stream b =
  unzips #[a] #b s

let unzip3 (#a #b: PR.typ) (#c: list PR.typ)
    (s: stream (a :: b :: c)): stream [a] & stream [b] & stream c =
  let (x, yz) = unzips #[a] #(b :: c) s in
  let (y, z)  = unzips #[b] #c yz in
  (x, y, z)

(* ----- Binding and recursion -------------------------------------------- *)

let let' (#a #b: list PR.typ)
    (e: stream a) (f: stream a -> stream b): stream b =
  fun n ->
    let (ev, n)    = e n in
    let (xs, n)    = fresh_vars a n in
    let sref: stream a = (fun m -> (PES.TTuple (L.map (fun (x: PES.svar) -> PES.SVar x) xs), m)) in
    let (bodyv, n) = f sref n in
    (PES.TLet a ev (close_vars 0 xs bodyv), n)

let mu (#a: list PR.typ) (f: stream a -> stream a): stream a =
  fun n ->
    let (xs, n)    = fresh_vars a n in
    let sref: stream a = (fun m -> (PES.TTuple (L.map (fun (x: PES.svar) -> PES.SVar x) xs), m)) in
    let (bodyv, n) = f sref n in
    (PES.TRec a (close_vars 0 xs bodyv), n)

let letrec (#a #b: list PR.typ)
    (f: stream a -> stream a) (cont: stream a -> stream b): stream b =
  let' (mu f) cont

(* ----- Nodes ------------------------------------------------------------ *)

let node (#args #results: list PR.typ)
    (head: string) (s: stream args): stream results =
  fun n ->
    let (t, n)     = s n in
    let (es, w, n) = components args t n in
    (w (PES.TStreamApp head es), n)

(* ----- Lowering --------------------------------------------------------- *)

let exp_of_stream (#a: list PR.typ) (s: stream a): PES.tterm =
  fst (s 0)
