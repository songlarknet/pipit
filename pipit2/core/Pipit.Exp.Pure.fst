module Pipit.Exp.Pure

module PR = Pipit.Exp.Prim
module N  = Pipit.Base.Context.Named

type pvar = string

[@@plugin]
type pterm =
  | PVar   : pvar      -> pterm
  | PValue : PR.value  -> pterm
  | PApp   : PR.prim -> list pterm -> pterm

type ty_context  = N.context PR.typ
type val_context = N.context PR.value

let ty_empty:  ty_context  = N.empty
let val_empty: val_context = N.empty

let rec pterm_ty (ctx: ty_context) (e: pterm): Tot (option PR.typ) (decreases e) =
  match e with
  | PVar x      -> N.lookup ctx x
  | PValue v    -> Some (PR.value_ty v)
  | PApp p args -> (match ty_args ctx args with
                   | Some tys -> PR.prim_ty p tys
                   | None     -> None)
and ty_args (ctx: ty_context) (args: list pterm): Tot (option (list PR.typ)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match pterm_ty ctx a, ty_args ctx tl with
               | Some t, Some ts -> Some (t :: ts)
               | _, _            -> None)

let rec pterm_sem (ctx: val_context) (e: pterm): Tot (option PR.value) (decreases e) =
  match e with
  | PVar x      -> N.lookup ctx x
  | PValue v    -> Some v
  | PApp p args -> (match sem_args ctx args with
                   | Some vs -> PR.prim_sem p vs
                   | None    -> None)
and sem_args (ctx: val_context) (args: list pterm): Tot (option (list PR.value)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match pterm_sem ctx a, sem_args ctx tl with
               | Some v, Some vs -> Some (v :: vs)
               | _, _            -> None)

let rec subst (x: pvar) (rhs: pterm) (body: pterm): Tot pterm (decreases body) =
  match body with
  | PVar y      -> if y = x then rhs else body
  | PValue _    -> body
  | PApp p args -> PApp p (subst_args x rhs args)
and subst_args (x: pvar) (rhs: pterm) (args: list pterm): Tot (list pterm) (decreases args) =
  match args with
  | []      -> []
  | a :: tl -> subst x rhs a :: subst_args x rhs tl
