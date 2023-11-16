(* Common subexpression elimination (CSE)
*)
module Pipit.Exp.Cse

// open Pipit.Prim.Table
// open Pipit.Prop.Base

// open Pipit.Exp.Base
// open Pipit.Exp.Bigstep
// open Pipit.Exp.Binding
// open Pipit.Exp.Causality
// open Pipit.Exp.Check

// module C  = Pipit.Context.Base
// module CR = Pipit.Context.Row
// module CP = Pipit.Context.Properties

// type binds (t: table) (c0: context t): (c: context t) -> Type =
//  | BindNil: binds t c0 []
//  | BindCons:
//    a: t.ty            ->
//    e: exp t c0 a       ->
//    c: context t       ->
//    binds t (a :: c0) c ->
//    binds t c0 (a :: c)


// let rec merge_binds (#t: table) (#c0 #c1 #c2: context t)
//   (b1: binds c0 c1)
//   (b2: binds (C.rev_acc c0 c1) c2)
//     : (c': context t & binds c0 c' & (C.index_lookup (C.rev_acc (C.rev_acc c0 c1) c2) -> C.index_lookup c'))
//   =
//   admit ()

// let rec take (e: exp t c a): (binds & exp_base t c a) =
//   match e with
//   | XBase b -> (BindNil, b)
//   | XApps es -> take_apps es
//   | XFby v e -> let (bs, ex) = take e in (bs ++ [XFby v ex], XVar 0)
//   | XMu e ->
//     let (bs, ex) = take e in
//     let (bs_lt, bs_ge) = split_on_var 0 bs in
//     (bs_lt, make bs_ge ex)
//   | XLet e1 e2 ->
//     let (bs1, ex1) = take e1 in
//     let (bs2, ex2) = take (lift e2 1 (length bs1)) in
//     let (bs2_lt, bs2_ge) = split_on_var 0 bs2 in
//     (bs1 ++ bs2_lt ++ [ex1] ++ bs2_ge, ex2)
//   | XContract status er eg ei ->
//     let (bsr, exr) = take er in
//     let (bsg, exg) = take eg in
//     let (bsg_lt, bsg_ge) = split_on_var 0 bsg in
//     (bsr ++ bsg_lt ++ [XContract status exr (make bsg_ge exg) ei], XVar 0)
//   | XCheck status ep ->
//     let (bsp, exp) = take ep in
//     (bsp ++ XCheck exp, XVar 0)

// let cse (#t: table) (#c: context t) (#a: t.ty) (e: exp t c a): Tot (exp t c a) (decreases e) =
//   admit ()

