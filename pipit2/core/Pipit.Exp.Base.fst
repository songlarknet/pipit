(* Core term representation: pure terms (`pterm`), value types (`typ`), a
   signature environment (`sigenv`), and a stratified stream / tuple term
   language (`sterm` / `tterm`) with locally-nameless binders and a decidable
   checker. Design notes and rationale: see Pipit.Exp.Base.md. *)
module Pipit.Exp.Base

module L = FStar.List.Tot

(* ----- Pure terms ------------------------------------------------------- *)

[@@plugin]
type lit =
  | LBool : bool -> lit
  | LInt  : int  -> lit
  | LBV   : nat -> nat -> lit

[@@plugin]
type pterm =
  | PVar : string -> pterm
  | PLit : lit -> pterm
  | PCon : string -> list pterm -> pterm
  | PApp : pterm -> list pterm -> pterm

(* ----- Value types ------------------------------------------------------ *)

[@@plugin]
type typ =
  | TBool : typ
  | TInt  : typ
  | TBV   : nat -> typ

(* ----- Signatures and environment --------------------------------------- *)

[@@plugin]
type funty = { args: list typ; result: typ }

[@@plugin]
type binder =
  | BConst  : typ -> binder
  | BStream : typ -> binder

[@@plugin]
type nodety = { params: list binder; results: list typ }

[@@plugin]
type sigenv = {
  prims: list (string & funty);
  nodes: list (string & nodety);
}

(* ----- Stream terms ----------------------------------------------------- *)

[@@plugin]
type svar = { svname: nat; svty: typ }

[@@plugin]
type sterm =
  | SPure    : pterm -> sterm
  | SVar     : svar -> sterm
  | SBVar    : nat -> sterm
  | SFby     : pterm -> sterm -> sterm
  | SPureApp : pterm -> list sterm -> sterm

[@@plugin]
type tterm =
  | TTuple     : list sterm -> tterm
  | TStreamApp : string -> list sterm -> tterm
  | TRec       : list typ -> tterm -> tterm
  | TLet       : list typ -> tterm -> tterm -> tterm

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

(* Base type of a literal. *)
let lit_ty (l: lit): typ =
  match l with
  | LBool _ -> TBool
  | LInt  _ -> TInt
  | LBV w _ -> TBV w

let infer_val (v: pterm): option typ =
  match v with
  | PLit l -> Some (lit_ty l)
  | _      -> None

let head_name (h: pterm): option string =
  match h with
  | PVar n          -> Some n
  | PApp (PVar n) _ -> Some n
  | _               -> None

let rec infer_s (env: sigenv) (ctx: list typ) (e: sterm): Tot (option typ) (decreases e) =
  match e with
  | SPure v         -> infer_val v
  | SVar x          -> Some x.svty
  | SBVar i         -> if i < L.length ctx then Some (L.index ctx i) else None
  | SFby v e'       -> (match infer_val v with
                       | Some a -> if infer_s env ctx e' = Some a then Some a else None
                       | None   -> None)
  | SPureApp h args -> (match head_name h with
                       | Some n -> (match L.assoc n env.prims with
                                   | Some ft -> if check_args env ctx args ft.args
                                               then Some ft.result else None
                                   | None    -> None)
                       | None   -> None)
and check_args (env: sigenv) (ctx: list typ) (args: list sterm) (tys: list typ)
: Tot bool (decreases args) =
  match args, tys with
  | [], []             -> true
  | a :: atl, t :: ttl -> infer_s env ctx a = Some t && check_args env ctx atl ttl
  | _, _               -> false
(* Check node arguments against parameter binders: a `BStream t` accepts any
   stream of type `t`; a `BConst t` accepts only a *constant* stream (`SPure`)
   of type `t`. *)
and check_node_args (env: sigenv) (ctx: list typ) (args: list sterm) (params: list binder): Tot bool (decreases args) =
  match args, params with
  | [], []                     -> true
  | a :: atl, BStream t :: ptl -> infer_s env ctx a = Some t && check_node_args env ctx atl ptl
  | a :: atl, BConst t :: ptl  ->
    (match a with SPure v -> infer_val v = Some t | _ -> false) && check_node_args env ctx atl ptl
  | _, _                       -> false

(* Tuple inference: `infer_t` gives the list of component types; layered on
   `infer_s`, never the reverse. *)
let rec infer_args (env: sigenv) (ctx: list typ) (args: list sterm)
: Tot (option (list typ)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match infer_s env ctx a, infer_args env ctx tl with
               | Some t, Some ts -> Some (t :: ts)
               | _, _            -> None)
and infer_t (env: sigenv) (ctx: list typ) (t: tterm): Tot (option (list typ)) (decreases t) =
  match t with
  | TTuple es          -> infer_args env ctx es
  | TStreamApp nm args -> (match L.assoc nm env.nodes with
                          | Some nt -> if check_node_args env ctx args nt.params
                                      then Some nt.results else None
                          | None    -> None)
  | TRec tys body      -> if infer_t env (L.append tys ctx) body = Some tys
                         then Some tys else None
  | TLet tys rhs bod   -> if infer_t env ctx rhs = Some tys
                         then infer_t env (L.append tys ctx) bod else None

(* `e` is well typed at `a` when inference agrees. *)
let well_typed (env: sigenv) (ctx: list typ) (e: sterm) (a: typ): prop =
  infer_s env ctx e == Some a
