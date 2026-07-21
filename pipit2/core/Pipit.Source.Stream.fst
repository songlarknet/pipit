module Pipit.Source.Stream

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source
module L   = FStar.List.Tot

type stream (ts: list PR.typ) = nat -> PES.term & nat

let fresh (a: list PR.typ) (n: nat): PES.svar & nat =
  ({ PES.svname = n; svty = a }, n + 1)

let rec proj_refs (g: PES.svar) (j: nat) (tys: list PR.typ)
: Tot (list PES.term) (decreases tys) =
  match tys with
  | []      -> []
  | _ :: tl -> PES.XProj j (PES.XVar g) :: proj_refs g (j + 1) tl

let refs (g: PES.svar): list PES.term =
  match g.svty with
  | [_] -> [PES.XVar g]
  | tys -> proj_refs g 0 tys

let atomize (a: PR.typ) (t: PES.term) (n: nat)
: PES.term & (PES.term -> PES.term) & nat =
  match t with
  | PES.XTuple [e] -> (e, (fun body -> body), n)
  | _ ->
    let (g, n) = fresh [a] n in
    (PES.XVar g, (fun body -> PES.XLet [a] t (PES.close g body)), n)

let components (ts: list PR.typ) (t: PES.term) (n: nat)
: list PES.term & (PES.term -> PES.term) & nat =
  match t with
  | PES.XTuple es -> (es, (fun body -> body), n)
  | _ ->
    let (g, n) = fresh ts n in
    (refs g, (fun body -> PES.XLet ts t (PES.close g body)), n)

let fvar (#a: PR.typ) (x: PES.svar): stream [a] =
  fun n -> (PES.XTuple [PES.XVar x], n)

let const (#a: PR.typ) (v: PP.pterm): stream [a] =
  fun n -> (PES.XTuple [PES.XPure v], n)

let fby (#a: PR.typ) (v: PP.pterm) (s: stream [a]): stream [a] =
  fun n ->
    let (t, n)    = s n in
    let (e, w, n) = atomize a t n in
    (w (PES.XTuple [PES.XFby v e]), n)

let liftP (#args: list PR.typ) (#result: PR.typ)
    (p: PR.prim) (s: stream args): stream [result] =
  fun n ->
    let (t, n)     = s n in
    let (es, w, n) = components args t n in
    (w (PES.XTuple [PES.XPrim p es]), n)

let zips (#xs #ys: list PR.typ) (x: stream xs) (y: stream ys): stream (L.append xs ys) =
  fun n ->
    let (tx, n)      = x n in
    let (exs, wx, n) = components xs tx n in
    let (ty, n)      = y n in
    let (eys, wy, n) = components ys ty n in
    (wx (wy (PES.XTuple (L.append exs eys))), n)

let unzips (#xs #ys: list PR.typ) (s: stream (L.append xs ys)): stream xs & stream ys =
  let k = L.length xs in
  ( (fun n ->
      let (t, n)     = s n in
      let (es, w, n) = components (L.append xs ys) t n in
      (w (PES.XTuple (fst (L.splitAt k es))), n))
  , (fun n ->
      let (t, n)     = s n in
      let (es, w, n) = components (L.append xs ys) t n in
      (w (PES.XTuple (snd (L.splitAt k es))), n)) )

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

let let' (#a #b: list PR.typ)
    (e: stream a) (f: stream a -> stream b): stream b =
  fun n ->
    let (ev, n)    = e n in
    let (g, n)     = fresh a n in
    let sref: stream a = (fun m -> (PES.XTuple (refs g), m)) in
    let (bodyv, n) = f sref n in
    (PES.XLet a ev (PES.close g bodyv), n)

let mu (#a: list PR.typ) (f: stream a -> stream a): stream a =
  fun n ->
    let (g, n)     = fresh a n in
    let sref: stream a = (fun m -> (PES.XTuple (refs g), m)) in
    let (bodyv, n) = f sref n in
    (PES.XMu a (PES.close g bodyv), n)

let letrec (#a #b: list PR.typ)
    (f: stream a -> stream a) (cont: stream a -> stream b): stream b =
  let' (mu f) cont

let node (#args #results: list PR.typ)
    (head: string) (s: stream args): stream results =
  fun n ->
    let (t, n)     = s n in
    let (es, w, n) = components args t n in
    (w (PES.XNode head es), n)

let exp_of_stream (#a: list PR.typ) (s: stream a): PES.term =
  fst (s 0)
