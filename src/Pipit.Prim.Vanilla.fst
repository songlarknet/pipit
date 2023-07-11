(* Primitive table for "vanilla" Pipit.
   This defines some basic types and primops, but nothing too fancy. These
   types are _unsound_, in that the verification uses mathematical integers and
   reals, but the generated C code uses fixed-width (machine) numbers.
*)
module Pipit.Prim.Vanilla

open Pipit.Prim.Table
module R = FStar.Real


type valtype =
 | TBool: valtype
 | TInt:  valtype
 | TReal: valtype
 | TPair: valtype -> valtype -> valtype

let is_arithtype (t: valtype) = match t with
 | TInt  | TReal     -> true
 | TBool | TPair _ _ -> false

let arithtype = t: valtype { is_arithtype t }

let rec typ_sem (t: valtype): eqtype = match t with
 | TBool -> bool
 | TInt  -> int
 | TReal -> R.real
 | TPair a b -> typ_sem a & typ_sem b


type prim_bool =
 | P'B'And     | P'B'Or
 | P'B'Implies | P'B'Not

type prim_arith =
 | P'A'Add | P'A'Sub | P'A'Div | P'A'Mul
 | P'A'Lt  | P'A'Le  | P'A'Gt  | P'A'Ge
 // negate? abs? trig? sqrt2?

type prim_tup =
 | P'T'Pair | P'T'Fst | P'T'Snd

type prim_valtype =
 | P'V'Eq | P'V'Ne | P'V'IfThenElse

type prim =
 | P'B: prim_bool -> prim
 | P'A: prim_arith -> arithtype -> prim
 | P'T: prim_tup -> valtype -> valtype -> prim
 | P'V: prim_valtype -> valtype -> prim


let prim_bool_types (p: prim_bool): funty valtype = match p with
 | P'B'Not -> [TBool], TBool
 | _       -> [TBool; TBool], TBool

let prim_arith_types (p: prim_arith) (at: arithtype): funty valtype = match p with
 | P'A'Add | P'A'Sub | P'A'Div | P'A'Mul -> [at; at], at
 | P'A'Lt  | P'A'Le  | P'A'Gt  | P'A'Ge  -> [at; at], TBool

let prim_tup_types (p: prim_tup) (a: valtype) (b: valtype): funty valtype = match p with
 | P'T'Pair -> [a; b], TPair a b
 | P'T'Fst  -> [TPair a b], a
 | P'T'Snd  -> [TPair a b], b

let prim_valtype_types (p: prim_valtype) (a: valtype): funty valtype = match p with
 | P'V'Eq | P'V'Ne -> [a; a], TBool
 | P'V'IfThenElse  -> [TBool; a; a], a

let prim_types (p: prim): funty valtype = match p with
 | P'B p'       -> prim_bool_types    p'
 | P'A p' at    -> prim_arith_types   p' at
 | P'T p' a b   -> prim_tup_types     p' a b
 | P'V p' a     -> prim_valtype_types p' a

let prim_bool_sem (p: prim_bool): funty_sem typ_sem (prim_bool_types p) = match p with
 | P'B'Not     -> fun (x: bool) -> not x
 // Low*/KRML doesn't like short-circuiting boolean operators (&&) (||) but it seems to be OK with if-then-else
 | P'B'And     -> fun x y -> if x then y else false
 | P'B'Or      -> fun x y -> if x then true else y
 | P'B'Implies -> fun x y -> if x then y else true

let prim_arith_sem (p: prim_arith) (at: arithtype): funty_sem typ_sem (prim_arith_types p at) = match at with
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

let prim_tup_sem (p: prim_tup) (a: valtype) (b: valtype): funty_sem typ_sem (prim_tup_types p a b) = match p with
 | P'T'Pair -> fun (x: typ_sem a) (y: typ_sem b) -> x, y
 | P'T'Fst  -> fun ((x, y) : typ_sem a & typ_sem b) -> x
 | P'T'Snd  -> fun ((x, y) : typ_sem a & typ_sem b) -> y

let prim_valtype_sem (p: prim_valtype) (a: valtype): funty_sem typ_sem (prim_valtype_types p a) = match p with
 | P'V'Eq         -> fun (x: typ_sem a) y -> x = y
 | P'V'Ne         -> fun (x: typ_sem a) y -> x <> y
 | P'V'IfThenElse -> fun p (x: typ_sem a) y -> if p then x else y

let prim_sem (p: prim): funty_sem typ_sem (prim_types p) = match p with
 | P'B p'     -> prim_bool_sem p'
 | P'A p' at  -> prim_arith_sem p' at
 | P'T p' a b -> prim_tup_sem p' a b
 | P'V p' a   -> prim_valtype_sem p' a

