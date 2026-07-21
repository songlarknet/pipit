module Pipit.Exp.Anf

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source
module L   = FStar.List.Tot

[@@plugin]
type atom =
  | AVar  : nat -> atom
  | APure : PP.pterm -> atom

[@@plugin]
type rhs =
  | RFby     : PP.pterm -> atom -> rhs
  | RPureApp : PR.prim -> list atom -> rhs

[@@plugin]
type cont =
  | CLet     : PR.typ -> rhs -> cont -> cont
  | CLetNode : string -> list atom -> list PR.typ -> cont -> cont
  | CRet     : list atom -> cont

type binding =
  | BLet  : PR.typ -> rhs -> binding
  | BNode : string -> list atom -> list PR.typ -> binding

let width (b: binding): nat =
  match b with
  | BLet _ _       -> 1
  | BNode _ _ tys  -> L.length tys

type state = { binds: list binding; next: nat }

let init_state: state = { binds = []; next = 0 }

let rec find_level (binds: list binding) (acc: nat) (target: binding)
: Tot (option nat) (decreases binds) =
  match binds with
  | []      -> None
  | b :: tl -> if b = target then Some acc else find_level tl (acc + width b) target

let emit (st: state) (b: binding): state & nat =
  match find_level st.binds 0 b with
  | Some lvl -> (st, lvl)
  | None     -> ({ binds = L.append st.binds [b]; next = st.next + width b }, st.next)

let rec proj_pairs (base: nat) (tys: list PR.typ): Tot (list (atom & PR.typ)) (decreases tys) =
  match tys with
  | []      -> []
  | t :: tl -> (AVar base, t) :: proj_pairs (base + 1) tl

let rec lower (env: PES.sigenv) (senv: list (list (atom & PR.typ))) (st: state) (e: PES.term)
: Tot (option (state & list (atom & PR.typ))) (decreases e) =
  match e with
  | PES.XPure v ->
    (match PP.pterm_ty PP.ty_empty v with
     | Some ty -> Some (st, [(APure v, ty)])
     | None    -> None)
  | PES.XBVar i ->
    if i < L.length senv then Some (st, L.index senv i) else None
  | PES.XFby v e' ->
    (match PP.pterm_ty PP.ty_empty v with
     | None    -> None
     | Some ty ->
       (match lower env senv st e' with
        | Some (st1, [(a, _)]) ->
          let (st2, lvl) = emit st1 (BLet ty (RFby v a)) in
          Some (st2, [(AVar lvl, ty)])
        | _ -> None))
  | PES.XPrim p args ->
    (match lower_scalars env senv st args with
     | None -> None
     | Some (st1, ats) ->
       let atoms = L.map fst ats in
       let tys   = L.map snd ats in
       (match PR.prim_ty p tys with
        | None     -> None
        | Some rty ->
          let (st2, lvl) = emit st1 (BLet rty (RPureApp p atoms)) in
          Some (st2, [(AVar lvl, rty)])))
  | PES.XTuple es -> lower_list env senv st es
  | PES.XNode nm args ->
    (match L.assoc nm env.nodes with
     | None    -> None
     | Some nt ->
       (match lower_scalars env senv st args with
        | None -> None
        | Some (st1, ats) ->
          let atoms = L.map fst ats in
          let (st2, base) = emit st1 (BNode nm atoms nt.results) in
          Some (st2, proj_pairs base nt.results)))
  | PES.XProj j e' ->
    (match lower env senv st e' with
     | None -> None
     | Some (st1, grp) -> if j < L.length grp then Some (st1, [L.index grp j]) else None)
  | PES.XLet _ d b ->
    (match lower env senv st d with
     | None -> None
     | Some (st1, grp) -> lower env (grp :: senv) st1 b)
  | PES.XContract _ _ _ i -> lower env senv st i
  | _ -> None  (* XVar, XMu, XCheck: deferred *)
and lower_scalars (env: PES.sigenv) (senv: list (list (atom & PR.typ))) (st: state) (args: list PES.term)
: Tot (option (state & list (atom & PR.typ))) (decreases args) =
  match args with
  | []      -> Some (st, [])
  | a :: tl ->
    (match lower env senv st a with
     | Some (st1, [(atom, ty)]) ->
       (match lower_scalars env senv st1 tl with
        | Some (st2, rest) -> Some (st2, (atom, ty) :: rest)
        | None             -> None)
     | _ -> None)
and lower_list (env: PES.sigenv) (senv: list (list (atom & PR.typ))) (st: state) (es: list PES.term)
: Tot (option (state & list (atom & PR.typ))) (decreases es) =
  match es with
  | []      -> Some (st, [])
  | e :: tl ->
    (match lower env senv st e with
     | None -> None
     | Some (st1, grp) ->
       (match lower_list env senv st1 tl with
        | None -> None
        | Some (st2, rest) -> Some (st2, L.append grp rest)))

let rec build_cont (binds: list binding) (tail: list atom): Tot cont (decreases binds) =
  match binds with
  | []                          -> CRet tail
  | BLet ty r :: tl             -> CLet ty r (build_cont tl tail)
  | BNode nm args outtys :: tl  -> CLetNode nm args outtys (build_cont tl tail)

[@@plugin]
let to_anf (env: PES.sigenv) (t: PES.term): option cont =
  match lower env [] init_state t with
  | Some (st, grp) -> Some (build_cont st.binds (L.map fst grp))
  | None           -> None
