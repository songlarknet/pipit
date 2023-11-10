(* Primitive table for "vanilla" Pipit.
   This defines some basic types and primops, but nothing too fancy. These
   types are _unsound_, in that the verification uses mathematical integers and
   reals, but the generated C code uses fixed-width (machine) numbers.
*)
module Pipit.Prim.Vanilla

open Pipit.Prim.Table
module R = FStar.Real
module PR = PipiRuntime.Prim.Bool

type valtype =
 | TBool: valtype
 | TInt:  valtype
 | TReal: valtype
 | TPair: valtype -> valtype -> valtype

let is_arithtype (t: valtype) = match t with
 | TInt  | TReal     -> true
 | TBool | TPair _ _ -> false

let arithtype = t: valtype { is_arithtype t }

let rec ty_sem (t: valtype): eqtype = match t with
 | TBool -> bool
 | TInt  -> int
 | TReal -> R.real
 | TPair a b -> ty_sem a & ty_sem b


type prim_bool =
 | P'B'And     | P'B'Or
 | P'B'Implies | P'B'Not

type prim_arith =
 | P'A'Add | P'A'Sub | P'A'Div | P'A'Mul
 | P'A'Lt  | P'A'Le  | P'A'Gt  | P'A'Ge
 // negate? abs? trig? sqrt2?

type prim_integral =
 | P'I'ModConst: nonzero -> prim_integral

type prim_tup =
 | P'T'Pair | P'T'Fst | P'T'Snd

type prim_valtype =
 | P'V'Eq | P'V'Ne | P'V'IfThenElse

type prim =
 | P'B: prim_bool -> prim
 | P'A: prim_arith -> arithtype -> prim
 | P'I: prim_integral -> prim
 | P'T: prim_tup -> valtype -> valtype -> prim
 | P'V: prim_valtype -> valtype -> prim

let f1 (t: valtype) = FTFun t (FTVal t)
let f2 (t: valtype) = FTFun t (FTFun t (FTVal t))
let p1 (t: valtype) = FTFun t (FTVal t)
let p2 (t: valtype) = FTFun t (FTFun t (FTVal TBool))


let prim_bool_ty (p: prim_bool): funty valtype = match p with
 | P'B'Not -> f1 TBool
 | _       -> f2 TBool

let prim_arith_ty (p: prim_arith) (at: arithtype): funty valtype = match p with
 | P'A'Add | P'A'Sub | P'A'Div | P'A'Mul -> f2 at
 | P'A'Lt  | P'A'Le  | P'A'Gt  | P'A'Ge  -> p2 at

let prim_integral_ty (p: prim_integral): funty valtype = f1 TInt

let prim_tup_ty (p: prim_tup) (a: valtype) (b: valtype): funty valtype = match p with
 | P'T'Pair -> FTFun a (FTFun b (FTVal (TPair a b)))
 | P'T'Fst  -> FTFun (TPair a b) (FTVal a)
 | P'T'Snd  -> FTFun (TPair a b) (FTVal b)

let prim_valtype_ty (p: prim_valtype) (a: valtype): funty valtype = match p with
 | P'V'Eq | P'V'Ne -> p2 a
 | P'V'IfThenElse  -> FTFun TBool (f2 a)

let prim_ty (p: prim): funty valtype = match p with
 | P'B p'       -> prim_bool_ty    p'
 | P'A p' at    -> prim_arith_ty   p' at
 | P'I p'       -> prim_integral_ty p'
 | P'T p' a b   -> prim_tup_ty     p' a b
 | P'V p' a     -> prim_valtype_ty p' a

let prim_bool_sem (p: prim_bool): funty_sem ty_sem (prim_bool_ty p) = match p with
 | P'B'Not     -> PR.p'b'not
 // Low*/KRML doesn't like short-circuiting boolean operators (&&) (||) but it seems to be OK with if-then-else
 | P'B'And     -> PR.p'b'and
 | P'B'Or      -> PR.p'b'or
 | P'B'Implies -> PR.p'b'implies

let prim_arith_sem (p: prim_arith) (at: arithtype): funty_sem ty_sem (prim_arith_ty p at) = match at with
 | TInt ->
  (match p with
  | P'A'Add -> fun x y -> x + y
  | P'A'Sub -> fun x y -> x - y
  | P'A'Div -> fun x y -> x / y
  | P'A'Mul -> fun x y -> Prims.op_Multiply x y
  | P'A'Lt  -> fun x y -> x <  y
  | P'A'Le  -> fun x y -> x <= y
  | P'A'Gt  -> fun x y -> x >  y
  | P'A'Ge  -> fun x y -> x >= y)
 | TReal ->
  R.(match p with
  | P'A'Add -> fun x y -> x +. y
  | P'A'Sub -> fun x y -> x -. y
  | P'A'Div -> fun x y -> x /. y
  | P'A'Mul -> fun x y -> x *. y
  | P'A'Lt  -> fun x y -> x <.  y
  | P'A'Le  -> fun x y -> x <=. y
  | P'A'Gt  -> fun x y -> x >.  y
  | P'A'Ge  -> fun x y -> x >=. y)

let prim_integral_sem (p: prim_integral): funty_sem ty_sem (prim_integral_ty p) =
  (match p with
   | P'I'ModConst div -> fun x -> x % div)

let prim_tup_sem (p: prim_tup) (a: valtype) (b: valtype): funty_sem ty_sem (prim_tup_ty p a b) = match p with
 | P'T'Pair -> fun (x: ty_sem a) (y: ty_sem b) -> x, y
 | P'T'Fst  -> fun ((x, y) : ty_sem a & ty_sem b) -> x
 | P'T'Snd  -> fun ((x, y) : ty_sem a & ty_sem b) -> y

let prim_valtype_sem (p: prim_valtype) (a: valtype): funty_sem ty_sem (prim_valtype_ty p a) = match p with
 | P'V'Eq         -> fun (x: ty_sem a) y -> x = y
 | P'V'Ne         -> fun (x: ty_sem a) y -> x <> y
 | P'V'IfThenElse -> PR.p'select #(ty_sem a)

let prim_sem (p: prim): funty_sem ty_sem (prim_ty p) = match p with
 | P'B p'     -> prim_bool_sem p'
 | P'A p' at  -> prim_arith_sem p' at
 | P'I p'     -> prim_integral_sem p'
 | P'T p' a b -> prim_tup_sem p' a b
 | P'V p' a   -> prim_valtype_sem p' a

let rec val_default (t: valtype): ty_sem t = match t with
 | TBool     -> false
 | TInt      -> 0
 | TReal     -> R.zero
 | TPair a b -> (val_default a, val_default b)

let table: table = {
   ty          = valtype;
   ty_sem      = ty_sem;

   prim        = prim;
   prim_ty     = prim_ty;
   prim_sem    = prim_sem;

   val_default = val_default;

   propty      = TBool;
}
