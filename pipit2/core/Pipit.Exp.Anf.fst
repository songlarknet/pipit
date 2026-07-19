(* Pipit.Exp.Anf -- an A-normal-form core IR and the normalizing lowering from
   a `tterm`, with common-subexpression elimination that recovers the sharing the
   shallow source layer loses.

   Why this exists. The source layer emits each output of a multi-output node
   call as its own `TLet`-binding of the *same* `TStreamApp` -- the projection
   idiom `TLet tys (TStreamApp ..) (TTuple [SBVar i])` (see
   `Pipit.Source.Stream.node22`). Because a term is a tree (not a DAG), that
   node-application subterm is *duplicated* wherever more than one of its outputs
   is used. So the sharing is recovered here, by a *multi-output* binding form,
   `CLetNode` (the `LetStreamApp` of the plan): lowering hoists each *distinct*
   node instantiation into one `CLetNode` and rewrites its projections to
   variable references. CSE is uniform -- every binding is hash-consed against
   the ones already emitted -- so ordinary common subexpressions collapse too.

   de Bruijn *levels*, not indices. Unlike `sterm` (whose `SBVar` counts binders
   inward, innermost = 0), an ANF `AVar` is a de Bruijn *level*: 0 is the
   *outermost* `CLet`/`CLetNode`. Levels are what make the append-only telescope
   construction sound -- emitting a new binding never shifts the atoms already
   built, which is exactly what lets CSE reuse an earlier binding's level. A
   consumer reads levels from the outside in.

   Scope. Full ANF (every `SPureApp` argument is named to an atom) over the
   first-order fragment: `SPure`, `SBVar`, `SFby`, `SPureApp`, and the tuple
   formers `TTuple` / `TStreamApp` / `TLet`. Recursion (the n-ary `TRec`
   group) is deferred -- faithful recursive ANF wants the register / transition-
   system view -- so the lowering is partial (`option`) and returns `None` on
   `TRec` (and on free `SVar`s). *)
module Pipit.Exp.Anf

module PEB = Pipit.Exp.Base
module L   = FStar.List.Tot

(* ----- ANF syntax ------------------------------------------------------- *)

(* A trivial operand: a bound stream (by de Bruijn level) or a constant pure
   value. `APure` subsumes literals, so there is no separate atom for those. *)
[@@plugin]
type atom =
  | AVar  : nat -> atom
  | APure : PEB.pterm -> atom

(* The right-hand side of a single-output binding: a delay or a single-output
   primitive / operator application, both over already-named atoms. *)
[@@plugin]
type rhs =
  | RFby     : PEB.pterm -> atom -> rhs
  | RPureApp : PEB.pterm -> list atom -> rhs

(* An A-normal continuation. `CLet` binds one flow; `CLetNode` instantiates a
   node once and binds its (list of) output flows; `CRet` is the tail, returning
   the term's output flows (a list, for multi-output node bodies). The `list typ`
   on `CLetNode` is the node's output types (all streams, so a plain type list
   suffices -- no binder kind needed). *)
[@@plugin]
type cont =
  | CLet     : PEB.typ -> rhs -> cont -> cont
  | CLetNode : string -> list atom -> list PEB.typ -> cont -> cont
  | CRet     : list atom -> cont

(* ----- Lowering state (an append-only, hash-consed telescope) ----------- *)

(* One emitted binding, paired with its width (number of output flows it binds):
   a `BLet` binds 1, a `BNode` binds one per output type. *)
type binding =
  | BLet  : PEB.typ -> rhs -> binding
  | BNode : string -> list atom -> list PEB.typ -> binding

let width (b: binding): nat =
  match b with
  | BLet _ _       -> 1
  | BNode _ _ tys  -> L.length tys

(* The telescope built so far (outermost binding first) and the next free level
   (= total width emitted). *)
type state = { binds: list binding; next: nat }

let init_state: state = { binds = []; next = 0 }

(* The base level of the first binding structurally equal to `target`, or `None`.
   `acc` is the running level (each binding advances it by its width). *)
let rec find_level (binds: list binding) (acc: nat) (target: binding)
: Tot (option nat) (decreases binds) =
  match binds with
  | []      -> None
  | b :: tl -> if b = target then Some acc else find_level tl (acc + width b) target

(* Hash-consing emit: reuse an existing structurally-equal binding's base level
   (CSE), else append the binding and return its fresh base level. *)
let emit (st: state) (b: binding): state & nat =
  match find_level st.binds 0 b with
  | Some lvl -> (st, lvl)
  | None     -> ({ binds = L.append st.binds [b]; next = st.next + width b }, st.next)

(* ----- Lowering sterm -> ANF -------------------------------------------- *)

(* The `i`-th projection atoms of a node call bound at base level `base`:
   `[AVar base; AVar (base+1); ..]`, one per result type. *)
let rec proj_atoms (base: nat) (tys: list PEB.typ): Tot (list atom) (decreases tys) =
  match tys with
  | []      -> []
  | _ :: tl -> AVar base :: proj_atoms (base + 1) tl

(* Pair up already-lowered atoms with their types for `senv` extension. *)
let rec zip_at (atoms: list atom) (tys: list PEB.typ): list (atom & PEB.typ) =
  match atoms, tys with
  | a :: atl, t :: ttl -> (a, t) :: zip_at atl ttl
  | _, _               -> []

(* `senv` maps a source de-Bruijn *index* to the ANF atom (and type) it lowered
   to; `st` is the telescope. Each call returns the updated telescope, the atom
   naming `e`'s (single) output, and its type. Partial: `None` on the deferred /
   ill-formed cases. `lower_t` is the tuple counterpart, returning one atom per
   component flow. *)
let rec lower (env: PEB.sigenv) (senv: list (atom & PEB.typ)) (st: state) (e: PEB.sterm)
: Tot (option (state & atom & PEB.typ)) (decreases e) =
  match e with
  | PEB.SPure v ->
    (match PEB.infer_val v with
     | Some ty -> Some (st, APure v, ty)
     | None    -> None)
  | PEB.SBVar i ->
    if i < L.length senv then (let (a, ty) = L.index senv i in Some (st, a, ty)) else None
  | PEB.SFby v e' ->
    (match PEB.infer_val v with
     | None    -> None
     | Some ty ->
       (match lower env senv st e' with
        | None -> None
        | Some (st1, a, _) ->
          let (st2, lvl) = emit st1 (BLet ty (RFby v a)) in
          Some (st2, AVar lvl, ty)))
  | PEB.SPureApp h args ->
    (match PEB.head_name h with
     | None    -> None
     | Some nm ->
       (match L.assoc nm env.prims with
        | None    -> None
        | Some ft ->
          (match lower_list env senv st args with
           | None -> None
           | Some (st1, atoms, _) ->
             let (st2, lvl) = emit st1 (BLet ft.result (RPureApp h atoms)) in
             Some (st2, AVar lvl, ft.result))))
  | _ -> None  (* SVar *)
and lower_t (env: PEB.sigenv) (senv: list (atom & PEB.typ)) (st: state) (t: PEB.tterm)
: Tot (option (state & list atom & list PEB.typ)) (decreases t) =
  match t with
  | PEB.TTuple es -> lower_list env senv st es
  | PEB.TStreamApp nm args ->
    (match L.assoc nm env.nodes with
     | None    -> None
     | Some nt ->
       (match lower_list env senv st args with
        | None -> None
        | Some (st1, atoms, _) ->
          let (st2, base) = emit st1 (BNode nm atoms nt.results) in
          Some (st2, proj_atoms base nt.results, nt.results)))
  | PEB.TLet _ rhs body ->
    (* the source let is inlined into `senv`; only `rhs`'s own bindings persist *)
    (match lower_t env senv st rhs with
     | None -> None
     | Some (st1, atoms, rtys) ->
       lower_t env (L.append (zip_at atoms rtys) senv) st1 body)
  | PEB.TRec _ _ -> None  (* deferred *)
and lower_list (env: PEB.sigenv) (senv: list (atom & PEB.typ)) (st: state) (es: list PEB.sterm)
: Tot (option (state & list atom & list PEB.typ)) (decreases es) =
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

(* Lower a closed, recursion-free (`TRec`) `tterm` to ANF, or `None` if
   out of scope. *)
[@@plugin]
let to_anf (env: PEB.sigenv) (t: PEB.tterm): option cont =
  match lower_t env [] init_state t with
  | Some (st, atoms, _) -> Some (build_cont st.binds atoms)
  | None                -> None
