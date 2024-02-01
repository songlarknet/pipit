module Pipit.System.Exp.Check.Base

open Pipit.Prim.Table
open Pipit.Exp.Base

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality

module PM  = Pipit.Prop.Metadata

module T   = FStar.Tactics

(*
   The invariant describes the transition system's state after it has been fed with all of `rows` as inputs.
*)
let rec check_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  (mode: PM.check_mode):
    Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> check_apps_invariant rows e1 mode

  | XFby v1 e2 ->
    check_invariant rows e2 mode

  | XMu e1 ->
    check_invariant (CR.zip2_cons (XC.lemma_bigsteps_total_vs rows e) rows) e1 mode

  | XLet b e1 e2 ->
    check_invariant rows e1 mode /\
    check_invariant (CR.zip2_cons (XC.lemma_bigsteps_total_vs rows e1) rows) e2 mode

  | XCheck ps e1 ->
    check_invariant rows e1 mode /\
    (PM.prop_status_contains mode ps ==> XB.bigstep_always rows e1)

  | XContract ps er eg eb ->
    let rows' = CR.zip2_cons (XC.lemma_bigsteps_total_vs rows eb) rows in
    (PM.prop_status_contains mode ps ==> XB.bigstep_always rows er) /\
    (PM.prop_status_contains mode PM.PSValid ==> XB.bigstep_always rows er ==> XB.bigstep_always rows' eg) /\
    check_invariant rows er mode /\
    check_invariant rows' eg mode

and check_apps_invariant
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e })
  (mode: PM.check_mode):
    Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 ->
    check_apps_invariant rows e1 mode /\
    check_invariant rows e2 mode

let rec check_init
    (#t: table) (#c: context t) (#a: t.ty)
    (e: exp t c a { XC.causal e })
    (mode: PM.check_mode)
    : Lemma (ensures check_invariant [] e mode)
      (decreases e) =
    let tx = SX.system_of_exp e in
    let rows: list (row c) = [] in
    match e with
    | XBase _ -> ()

    | XApps e1 ->
      check_apps_init e1 (fun r () -> r) mode;
      ()

    | XFby v1 e2 ->
      check_init e2 mode

    | XMu e1 ->
      check_init e1 mode;
      ()

    | XLet b e1 e2 ->
      check_init e1 mode;
      check_init e2 mode;
      ()

    | XCheck _ e1 ->
      check_init e1 mode

    | XContract ps er eg eb ->
      check_init er mode;
      check_init eg mode;
      ()

and check_apps_init
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    (mode: PM.check_mode)
    : Lemma (ensures
        check_apps_invariant [] e mode)
      (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let f' = SX.system_of_exp_apps_distr f in
    check_apps_init e1 f' mode;
    check_init e2 mode;
    ()

let eval_step
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (row1: row c)
    (e: exp t c a { XC.causal e })
    (s: SB.option_type_sem (SX.state_of_exp e) { SXP.system_of_exp_invariant rows e s })
    : stp: SB.step_result (SX.state_of_exp e) (t.ty_sem a) {
      stp.v == (XC.lemma_bigstep_total_v (row1 :: rows) e) /\ SXP.system_of_exp_invariant (row1 :: rows) e stp.s
    } =
  let orcl = SXP.step_oracle (row1 :: rows) e in
  SXP.invariant_step rows row1 e s;
  (SX.system_of_exp e).step row1 orcl s


let eval_step_apps
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (rows: list (row c))
    (row1: row c)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    (inp0: inp)
    (s: SB.option_type_sem (SX.state_of_exp_apps e) { SXP.system_of_exp_apps_invariant rows e s })
    : stp: SB.step_result (SX.state_of_exp_apps e) res {
      stp.v == f (dfst (XC.lemma_bigstep_apps_total (row1 :: rows) e)) inp0 /\
      SXP.system_of_exp_apps_invariant (row1 :: rows) e stp.s
    } =
  let orcl = SXP.step_apps_oracle (row1 :: rows) e in
  SXP.invariant_step_apps rows row1 e f inp0 s;
  (SX.system_of_exp_apps e f).step (inp0, row1) orcl s
