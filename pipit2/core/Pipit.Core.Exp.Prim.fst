module Pipit.Core.Exp.Prim

[@@plugin]
type typ =
  | TBool : typ
  | TInt  : typ
  | TBV   : nat -> typ

[@@plugin]
type value =
  | VBool : bool -> value
  | VInt  : int  -> value
  | VBV   : (w: nat) -> nat -> value

let value_ty (v: value): typ =
  match v with
  | VBool _ -> TBool
  | VInt  _ -> TInt
  | VBV w _ -> TBV w

[@@plugin]
type prim =
  | PAnd    : prim
  | POr     : prim
  | PNot    : prim
  | PIntAdd : prim
  | PIntSub : prim
  | PIntLe  : prim
  | PBVAdd  : prim

let prim_ty (p: prim) (args: list typ): option typ =
  match p, args with
  | PAnd,    [TBool; TBool] -> Some TBool
  | POr,     [TBool; TBool] -> Some TBool
  | PNot,    [TBool]        -> Some TBool
  | PIntAdd, [TInt; TInt]   -> Some TInt
  | PIntSub, [TInt; TInt]   -> Some TInt
  | PIntLe,  [TInt; TInt]   -> Some TBool
  | PBVAdd,  [TBV a; TBV b] -> if a = b then Some (TBV a) else None
  | _, _                    -> None

let prim_sem (p: prim) (args: list value): option value =
  match p, args with
  | PAnd,    [VBool a; VBool b] -> Some (VBool (a && b))
  | POr,     [VBool a; VBool b] -> Some (VBool (a || b))
  | PNot,    [VBool a]          -> Some (VBool (not a))
  | PIntAdd, [VInt a; VInt b]   -> Some (VInt (a + b))
  | PIntSub, [VInt a; VInt b]   -> Some (VInt (a - b))
  | PIntLe,  [VInt a; VInt b]   -> Some (VBool (a <= b))
  | PBVAdd,  [VBV wa a; VBV wb b] ->
    if wa = wb then Some (VBV wa ((a + b) % pow2 wa)) else None
  | _, _                        -> None
