module Pipit.Norm.FromExp

open Pipit.Prim.Table

open Pipit.Norm.Context
open Pipit.Norm.Defs
open Pipit.Norm.Exp

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties

module X  = Pipit.Exp.Base

// Hard to write down definitions ahead of time, as it depends on how the
// recursive definitions are split
// let rec dcontext_of_exp
//   (#t: table) (#c: context t) (#ty: t.ty)
//   (e: X.exp t c ty)
//     : context t =
//   match e with
//   | X.XVal _ -> []
//   | X.XBVar _ -> []
//   | X.XVar _ -> []
//   | X.XPrim _ -> []
//   | X.XApp e e' ->
//     let c0 = dcontext_of_exp e `C.append` dcontext_of_exp e' in
//     c0 // `C.append` result type...
//   | X.XFby v e' ->
//     // (X.XFby?.valty e) ::
//       dcontext_of_exp e'
//   | X.XThen e e' ->
//     dcontext_of_exp e `C.append` dcontext_of_exp e'
//   | X.XMu e' ->
//     dcontext_of_exp

// let split
//   (#t: table) (#c #cd: context t) (#ty: t.ty)
//   (n: norm_base t (NC c (ty :: cd)) ty):
//     cd1: context t & cd2: context t { cd = cd1 `C.append` cd2 } &
//     d1: norm_base t (NC c cd1) ty &
//     // e1: nexp_base t (NC c cd1) ty &
//     d2: nsys t (NC c cd2)


let translate
  (#t: table) (#c: context t) (#ty: t.ty)
  (e: X.val_exp t c ty):
    c': context t & norm_base t (NC c c') ty =
  admit ()
