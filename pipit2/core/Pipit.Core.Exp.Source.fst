module Pipit.Core.Exp.Source

module PR = Pipit.Core.Exp.Prim
module PP = Pipit.Core.Exp.Pure
module PM = Pipit.Base.Prop.Metadata
module L  = FStar.List.Tot

[@@plugin]
type binder =
  | BConst  : PP.pvar -> PR.typ -> binder
  | BStream : PR.typ -> binder

[@@plugin]
type svar = { svname: nat; svty: list PR.typ }

[@@plugin]
type term =
  | XPure     : PP.pterm -> term
  | XVar      : svar -> term
  | XBVar     : nat -> term
  | XFby      : list PP.pterm -> list term -> term
  | XPrim     : PR.prim -> term -> term
  | XTuple    : list term -> term
  | XNode     : string -> list term -> term
  | XProj     : nat -> term -> term
  | XMu       : list PR.typ -> term -> term
  | XLet      : list PR.typ -> term -> term -> term
  | XContract : PM.contract_status -> term -> term -> term -> term
  | XCheck    : PM.prop_status -> term -> term

[@@plugin]
type node = { params: list binder; results: list PR.typ; body: term }

[@@plugin]
type sigenv = { nodes: list (string & node) }
let mk_proj (j: nat) (e: term): term =
  match e with
  | XTuple es -> if j < L.length es then L.index es j else XProj j e
  | _         -> XProj j e

let rec close_rec (k: nat) (x: svar) (e: term): Tot term (decreases e) =
  match e with
  | XPure _           -> e
  | XVar y            -> if y = x then XBVar k else e
  | XBVar _           -> e
  | XFby v0s es       -> XFby v0s (close_args k x es)
  | XPrim p arg       -> XPrim p (close_rec k x arg)
  | XTuple es         -> XTuple (close_args k x es)
  | XNode nm args     -> XNode nm (close_args k x args)
  | XProj j e'        -> XProj j (close_rec k x e')
  | XMu tys body      -> XMu tys (close_rec (k + 1) x body)
  | XLet tys rhs bod  -> XLet tys (close_rec k x rhs) (close_rec (k + 1) x bod)
  | XContract s r g i -> XContract s (close_rec k x r) (close_rec (k + 1) x g) (close_rec k x i)
  | XCheck s e'       -> XCheck s (close_rec k x e')
and close_args (k: nat) (x: svar) (args: list term): Tot (list term) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> close_rec k x a :: close_args k x tl

let rec open_rec (k: nat) (u: term) (e: term): Tot term (decreases e) =
  match e with
  | XPure _           -> e
  | XVar _            -> e
  | XBVar i           -> if i = k then u else e
  | XFby v0s es       -> XFby v0s (open_args k u es)
  | XPrim p arg       -> XPrim p (open_rec k u arg)
  | XTuple es         -> XTuple (open_args k u es)
  | XNode nm args     -> XNode nm (open_args k u args)
  | XProj j e'        -> mk_proj j (open_rec k u e')
  | XMu tys body      -> XMu tys (open_rec (k + 1) u body)
  | XLet tys rhs bod  -> XLet tys (open_rec k u rhs) (open_rec (k + 1) u bod)
  | XContract s r g i -> XContract s (open_rec k u r) (open_rec (k + 1) u g) (open_rec k u i)
  | XCheck s e'       -> XCheck s (open_rec k u e')
and open_args (k: nat) (u: term) (args: list term): Tot (list term) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> open_rec k u a :: open_args k u tl

let close (x: svar) (e: term): term = close_rec 0 x e

let open_var (x: svar) (e: term): term = open_rec 0 (XVar x) e

let subst_tuple (def: term) (body: term): term = open_rec 0 def body

let rec psubst (x: PP.pvar) (r: PP.pterm) (e: term): Tot term (decreases e) =
  match e with
  | XPure p            -> XPure (PP.subst x r p)
  | XVar _             -> e
  | XBVar _            -> e
  | XFby v0s es        -> XFby (PP.subst_args x r v0s) (psubst_args x r es)
  | XPrim p arg        -> XPrim p (psubst x r arg)
  | XTuple es          -> XTuple (psubst_args x r es)
  | XNode nm args      -> XNode nm (psubst_args x r args)
  | XProj j e'         -> XProj j (psubst x r e')
  | XMu tys body       -> XMu tys (psubst x r body)
  | XLet tys rhs bod   -> XLet tys (psubst x r rhs) (psubst x r bod)
  | XContract s rl g i -> XContract s (psubst x r rl) (psubst x r g) (psubst x r i)
  | XCheck s e'        -> XCheck s (psubst x r e')
and psubst_args (x: PP.pvar) (r: PP.pterm) (args: list term): Tot (list term) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> psubst x r a :: psubst_args x r tl

let rec inst_streams (params: list binder) (args: list term): Tot (list term) (decreases params) =
  match params, args with
  | BStream _ :: ptl, a :: atl  -> a :: inst_streams ptl atl
  | BConst _ _ :: ptl, _ :: atl -> inst_streams ptl atl
  | _, _                        -> []

let rec inst_consts (params: list binder) (args: list term) (body: term): Tot term (decreases params) =
  match params, args with
  | BConst x _ :: ptl, a :: atl ->
    (match a with
     | XPure r -> inst_consts ptl atl (psubst x r body)
     | _       -> inst_consts ptl atl body)
  | BStream _ :: ptl, _ :: atl  -> inst_consts ptl atl body
  | _, _                        -> body

let inst_node (params: list binder) (args: list term) (body: term): term =
  subst_tuple (XTuple (inst_streams params args)) (inst_consts params args body)

let rec infer (env: sigenv) (ctx: list (list PR.typ)) (e: term)
: Tot (option (list PR.typ)) (decreases e) =
  match e with
  | XPure p        -> (match PP.pterm_ty PP.ty_empty p with
                      | Some a -> Some [a]
                      | None   -> None)
  | XVar x         -> Some x.svty
  | XBVar i        -> if i < L.length ctx then Some (L.index ctx i) else None
  | XFby v0s es    -> (match PP.ty_args PP.ty_empty v0s, infer_scalars env ctx es with
                      | Some ts, Some ts' -> if ts = ts' then Some ts else None
                      | _, _              -> None)
  | XPrim p arg    -> (match infer env ctx arg with
                      | Some tys -> (match PR.prim_ty p tys with
                                    | Some r -> Some [r]
                                    | None   -> None)
                      | None     -> None)
  | XTuple es      -> infer_widths env ctx es
  | XNode nm args  -> (match L.assoc nm env.nodes with
                      | Some nt -> if check_node_args env ctx args nt.params
                                  then Some nt.results else None
                      | None    -> None)
  | XProj j e'     -> (match infer env ctx e' with
                      | Some tys -> if j < L.length tys then Some [L.index tys j] else None
                      | None     -> None)
  | XMu tys body   -> if infer env (tys :: ctx) body = Some tys then Some tys else None
  | XLet tys d b   -> if infer env ctx d = Some tys
                     then infer env (tys :: ctx) b else None
  | XContract s r g i ->
    (match infer env ctx i with
     | Some tys -> if infer env ctx r = Some [PR.TBool] && infer env (tys :: ctx) g = Some [PR.TBool]
                  then Some tys else None
     | None     -> None)
  | XCheck s e'    -> if infer env ctx e' = Some [PR.TBool] then Some [] else None
and infer_scalars (env: sigenv) (ctx: list (list PR.typ)) (args: list term)
: Tot (option (list PR.typ)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match infer env ctx a, infer_scalars env ctx tl with
               | Some [t], Some ts -> Some (t :: ts)
               | _, _              -> None)
and infer_widths (env: sigenv) (ctx: list (list PR.typ)) (es: list term)
: Tot (option (list PR.typ)) (decreases es) =
  match es with
  | []      -> Some []
  | e :: tl -> (match infer env ctx e, infer_widths env ctx tl with
               | Some w, Some ws -> Some (L.append w ws)
               | _, _            -> None)
and check_node_args (env: sigenv) (ctx: list (list PR.typ)) (args: list term) (params: list binder)
: Tot bool (decreases args) =
  match args, params with
  | [], []                     -> true
  | a :: atl, BStream t :: ptl -> infer env ctx a = Some [t] && check_node_args env ctx atl ptl
  | a :: atl, BConst _ t :: ptl  ->
    (match a with XPure v -> PP.pterm_ty PP.ty_empty v = Some t | _ -> false)
    && check_node_args env ctx atl ptl
  | _, _                       -> false

let well_typed (env: sigenv) (ctx: list (list PR.typ)) (e: term) (w: list PR.typ): prop =
  infer env ctx e == Some w
