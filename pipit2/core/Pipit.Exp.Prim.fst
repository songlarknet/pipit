(* Value types, ground values, and the closed set of built-in primitives with
   their (partial) typing rule `prim_ty` and evaluator `prim_sem`. These are the
   "interpreted" operators the whole pipeline may fold, type, and reason about;
   user-defined operators (uninterpreted) are a later addition and live
   elsewhere. Design notes and rationale: see Pipit.Exp.Prim.md. *)
module Pipit.Exp.Prim

(* ----- Value types ------------------------------------------------------ *)

[@@plugin]
type typ =
  | TBool : typ
  | TInt  : typ
  | TBV   : nat -> typ

(* ----- Ground values ---------------------------------------------------- *)

(* A `VBV w n` denotes the bit vector `n mod 2^w`; the payload is kept as a
   plain `nat` (matching the first-order `[@@plugin]` embedding) and reduced on
   demand by `prim_sem`. *)
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

(* ----- Built-in primitives ---------------------------------------------- *)

(* Pseudo-polymorphic: each `PBV*` works at any width, resolved from its operand
   types by `prim_ty`. The set is closed (no user-defined case). *)
[@@plugin]
type prim =
  | PAnd    : prim
  | POr     : prim
  | PNot    : prim
  | PIntAdd : prim
  | PIntSub : prim
  | PIntLe  : prim
  | PBVAdd  : prim

(* Typing rule over operand types: partial, and the sole authority on a prim's
   arity and result type. *)
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

(* Evaluator: total in the (`prim`, well-typed argument list) it accepts,
   `None` off that domain. Agrees with `prim_ty` by construction. *)
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
