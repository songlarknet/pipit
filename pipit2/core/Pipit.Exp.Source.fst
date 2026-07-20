(* Source core: a signature environment (`sigenv`) and a stratified stream /
   tuple term language (`sterm` / `tterm`) with locally-nameless binders and a
   decidable checker. This is the frontend, non-normalised language; value
   types, values, and primitives live in `Pipit.Exp.Prim`, pure terms in
   `Pipit.Exp.Pure`. Design notes and rationale: see Pipit.Exp.Source.md. *)
module Pipit.Exp.Source

module PR = Pipit.Exp.Prim
module PP = Pipit.Exp.Pure
module L  = FStar.List.Tot

(* ----- Signatures and environment --------------------------------------- *)

[@@plugin]
type binder =
  | BConst  : PR.typ -> binder
  | BStream : PR.typ -> binder

[@@plugin]
type nodety = { params: list binder; results: list PR.typ }

[@@plugin]
type sigenv = { nodes: list (string & nodety) }

(* ----- Stream terms ----------------------------------------------------- *)

[@@plugin]
type svar = { svname: nat; svty: PR.typ }

[@@plugin]
type sterm =
  | SPure    : PP.pterm -> sterm
  | SVar     : svar -> sterm
  | SBVar    : nat -> sterm
  | SFby     : PP.pterm -> sterm -> sterm
  | SPureApp : PR.prim -> list sterm -> sterm

[@@plugin]
type tterm =
  | TTuple     : list sterm -> tterm
  | TStreamApp : string -> list sterm -> tterm
  | TRec       : list PR.typ -> tterm -> tterm
  | TLet       : list PR.typ -> tterm -> tterm -> tterm

(* ----- Locally-nameless open / close (object binders only) -------------- *)

let rec close_rec_s (k: nat) (x: svar) (e: sterm): Tot sterm (decreases e) =
  match e with
  | SPure _         -> e
  | SVar y          -> if y = x then SBVar k else e
  | SBVar _         -> e
  | SFby v e'       -> SFby v (close_rec_s k x e')
  | SPureApp h args -> SPureApp h (close_args_s k x args)
and close_args_s (k: nat) (x: svar) (args: list sterm): Tot (list sterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> close_rec_s k x a :: close_args_s k x tl

let rec close_rec_t (k: nat) (x: svar) (t: tterm): Tot tterm (decreases t) =
  match t with
  | TTuple es          -> TTuple (close_args_s k x es)
  | TStreamApp nm args -> TStreamApp nm (close_args_s k x args)
  | TRec tys body      -> TRec tys (close_rec_t (k + L.length tys) x body)
  | TLet tys rhs bod   -> TLet tys (close_rec_t k x rhs) (close_rec_t (k + L.length tys) x bod)

let rec open_rec_s (k: nat) (u: sterm) (e: sterm): Tot sterm (decreases e) =
  match e with
  | SPure _         -> e
  | SVar _          -> e
  | SBVar i         -> if i = k then u else e
  | SFby v e'       -> SFby v (open_rec_s k u e')
  | SPureApp h args -> SPureApp h (open_args_s k u args)
and open_args_s (k: nat) (u: sterm) (args: list sterm): Tot (list sterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> open_rec_s k u a :: open_args_s k u tl

let rec open_rec_t (k: nat) (u: sterm) (t: tterm): Tot tterm (decreases t) =
  match t with
  | TTuple es          -> TTuple (open_args_s k u es)
  | TStreamApp nm args -> TStreamApp nm (open_args_s k u args)
  | TRec tys body      -> TRec tys (open_rec_t (k + L.length tys) u body)
  | TLet tys rhs bod   -> TLet tys (open_rec_t k u rhs) (open_rec_t (k + L.length tys) u bod)

(* Close `x` into a fresh outermost binder (index 0) of a single stream. *)
let close (x: svar) (e: sterm): sterm = close_rec_s 0 x e

(* Open the outermost binder (index 0) with the free variable `x`. *)
let open_var (x: svar) (e: sterm): sterm = open_rec_s 0 (SVar x) e

(* ----- Type checking (decidable, environment-driven) -------------------- *)

let rec infer_s (env: sigenv) (ctx: list PR.typ) (e: sterm): Tot (option PR.typ) (decreases e) =
  match e with
  | SPure v         -> PP.infer_p v
  | SVar x          -> Some x.svty
  | SBVar i         -> if i < L.length ctx then Some (L.index ctx i) else None
  | SFby v e'       -> (match PP.infer_p v with
                       | Some a -> if infer_s env ctx e' = Some a then Some a else None
                       | None   -> None)
  | SPureApp p args -> (match infer_sargs env ctx args with
                       | Some tys -> PR.prim_ty p tys
                       | None     -> None)
and infer_sargs (env: sigenv) (ctx: list PR.typ) (args: list sterm)
: Tot (option (list PR.typ)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match infer_s env ctx a, infer_sargs env ctx tl with
               | Some t, Some ts -> Some (t :: ts)
               | _, _            -> None)
(* Check node arguments against parameter binders: a `BStream t` accepts any
   stream of type `t`; a `BConst t` accepts only a *constant* stream (`SPure`)
   of type `t`. *)
and check_node_args (env: sigenv) (ctx: list PR.typ) (args: list sterm) (params: list binder)
: Tot bool (decreases args) =
  match args, params with
  | [], []                     -> true
  | a :: atl, BStream t :: ptl -> infer_s env ctx a = Some t && check_node_args env ctx atl ptl
  | a :: atl, BConst t :: ptl  ->
    (match a with SPure v -> PP.infer_p v = Some t | _ -> false) && check_node_args env ctx atl ptl
  | _, _                       -> false

(* Tuple inference: `infer_t` gives the list of component types; layered on
   `infer_s`, never the reverse. *)
let rec infer_t (env: sigenv) (ctx: list PR.typ) (t: tterm): Tot (option (list PR.typ)) (decreases t) =
  match t with
  | TTuple es          -> infer_sargs env ctx es
  | TStreamApp nm args -> (match L.assoc nm env.nodes with
                          | Some nt -> if check_node_args env ctx args nt.params
                                      then Some nt.results else None
                          | None    -> None)
  | TRec tys body      -> if infer_t env (L.append tys ctx) body = Some tys
                         then Some tys else None
  | TLet tys rhs bod   -> if infer_t env ctx rhs = Some tys
                         then infer_t env (L.append tys ctx) bod else None

(* `e` is well typed at `a` when inference agrees. *)
let well_typed (env: sigenv) (ctx: list PR.typ) (e: sterm) (a: PR.typ): prop =
  infer_s env ctx e == Some a
