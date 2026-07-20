(* Pipit.Exp.Anf -- an A-normal-form core IR and the normalizing lowering from a
   `tterm`, with CSE that recovers the sharing the shallow source layer loses.
   Design notes and rationale: see Pipit.Exp.Anf.md. *)
module Pipit.Exp.Anf

module PR  = Pipit.Exp.Prim
module PP  = Pipit.Exp.Pure
module PES = Pipit.Exp.Source
module L   = FStar.List.Tot

(* ----- ANF syntax ------------------------------------------------------- *)

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

(* ----- Lowering state (an append-only, hash-consed telescope) ----------- *)

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

(* ----- Lowering sterm -> ANF -------------------------------------------- *)

let rec proj_atoms (base: nat) (tys: list PR.typ): Tot (list atom) (decreases tys) =
  match tys with
  | []      -> []
  | _ :: tl -> AVar base :: proj_atoms (base + 1) tl

let rec zip_at (atoms: list atom) (tys: list PR.typ): list (atom & PR.typ) =
  match atoms, tys with
  | a :: atl, t :: ttl -> (a, t) :: zip_at atl ttl
  | _, _               -> []

let rec lower (env: PES.sigenv) (senv: list (atom & PR.typ)) (st: state) (e: PES.sterm)
: Tot (option (state & atom & PR.typ)) (decreases e) =
  match e with
  | PES.SPure v ->
    (match PP.infer_p v with
     | Some ty -> Some (st, APure v, ty)
     | None    -> None)
  | PES.SBVar i ->
    if i < L.length senv then (let (a, ty) = L.index senv i in Some (st, a, ty)) else None
  | PES.SFby v e' ->
    (match PP.infer_p v with
     | None    -> None
     | Some ty ->
       (match lower env senv st e' with
        | None -> None
        | Some (st1, a, _) ->
          let (st2, lvl) = emit st1 (BLet ty (RFby v a)) in
          Some (st2, AVar lvl, ty)))
  | PES.SPureApp p args ->
    (match lower_list env senv st args with
     | None -> None
     | Some (st1, atoms, tys) ->
       (match PR.prim_ty p tys with
        | None     -> None
        | Some rty ->
          let (st2, lvl) = emit st1 (BLet rty (RPureApp p atoms)) in
          Some (st2, AVar lvl, rty)))
  | _ -> None  (* SVar *)
and lower_t (env: PES.sigenv) (senv: list (atom & PR.typ)) (st: state) (t: PES.tterm)
: Tot (option (state & list atom & list PR.typ)) (decreases t) =
  match t with
  | PES.TTuple es -> lower_list env senv st es
  | PES.TStreamApp nm args ->
    (match L.assoc nm env.nodes with
     | None    -> None
     | Some nt ->
       (match lower_list env senv st args with
        | None -> None
        | Some (st1, atoms, _) ->
          let (st2, base) = emit st1 (BNode nm atoms nt.results) in
          Some (st2, proj_atoms base nt.results, nt.results)))
  | PES.TLet _ rhs body ->
    (* the source let is inlined into `senv`; only `rhs`'s own bindings persist *)
    (match lower_t env senv st rhs with
     | None -> None
     | Some (st1, atoms, rtys) ->
       lower_t env (L.append (zip_at atoms rtys) senv) st1 body)
  | PES.TRec _ _ -> None  (* deferred *)
and lower_list (env: PES.sigenv) (senv: list (atom & PR.typ)) (st: state) (es: list PES.sterm)
: Tot (option (state & list atom & list PR.typ)) (decreases es) =
  match es with
  | []      -> Some (st, [], [])
  | e :: tl ->
    (match lower env senv st e with
     | None -> None
     | Some (st1, a, ty) ->
       (match lower_list env senv st1 tl with
        | None -> None
        | Some (st2, atoms, tys) -> Some (st2, a :: atoms, ty :: tys)))

(* Fold the finished telescope (outermost first) into nested lets over `tail`. *)
let rec build_cont (binds: list binding) (tail: list atom): Tot cont (decreases binds) =
  match binds with
  | []                          -> CRet tail
  | BLet ty r :: tl             -> CLet ty r (build_cont tl tail)
  | BNode nm args outtys :: tl  -> CLetNode nm args outtys (build_cont tl tail)

[@@plugin]
let to_anf (env: PES.sigenv) (t: PES.tterm): option cont =
  match lower_t env [] init_state t with
  | Some (st, atoms, _) -> Some (build_cont st.binds atoms)
  | None                -> None
