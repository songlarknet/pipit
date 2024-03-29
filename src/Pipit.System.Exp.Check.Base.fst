(* Properties about checks on translated systems. The main theorem is that any
  checks we prove on the translated system also hold on the original
  expression. See Pipit.System.Exp.Check.Entailment. *)
module Pipit.System.Exp.Check.Base

open Pipit.Prim.Table
open Pipit.Exp.Base

module CR  = Pipit.Context.Row

module SB  = Pipit.System.Base
module SI  = Pipit.System.Ind
module SX  = Pipit.System.Exp
module SXP = Pipit.System.Exp.Properties

module XB  = Pipit.Exp.Bigstep
module XC  = Pipit.Exp.Causality

module PM  = Pipit.Prop.Metadata

module T   = FStar.Tactics

(*
  This invariant describes the properties of the transition system evaluation
  after it has been fed with all of `rows` as inputs. It is very similar to the
  checked semantics in Pipit.Exp.Checked.Base, but it's a bit simpler. The
  proofs only apply to causal expressions, so we can use the "evaluator"
  instead of the bigsteps relation. Also, we only have to deal with contract
  instances here, rather than both definitions and instances.
*)
let rec check_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (mode: PM.check_mode)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  : Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> check_apps_invariant mode rows e1

  | XFby v1 e2 ->
    check_invariant mode rows e2

  | XMu e1 ->
    check_invariant mode (CR.extend1 (XC.lemma_bigsteps_total_vs rows e) rows) e1

  | XLet b e1 e2 ->
    check_invariant mode rows e1 /\
    check_invariant mode (CR.extend1 (XC.lemma_bigsteps_total_vs rows e1) rows) e2

  | XCheck ps e1 ->
    check_invariant mode rows e1 /\
    (PM.prop_status_contains mode ps ==> XB.bigstep_always rows e1)

  | XContract ps er eg eb ->
    let rows' = CR.extend1 (XC.lemma_bigsteps_total_vs rows eb) rows in
    (PM.prop_status_contains mode ps ==> XB.bigstep_always rows er) /\
    check_invariant mode rows er /\
    (PM.prop_status_contains mode PM.PSValid ==> XB.bigstep_always rows er ==> XB.bigstep_always rows' eg) /\
    // Unlike checked semantics, we do not need to check the body here
    (XB.bigstep_always rows er ==> check_invariant mode rows' eg)

and check_apps_invariant
  (#t: table) (#c: context t) (#a: funty t.ty)
  (mode: PM.check_mode)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e })
  : Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 ->
    check_apps_invariant mode rows e1 /\
    check_invariant mode rows e2

let rec check_init
    (#t: table) (#c: context t) (#a: t.ty)
    (mode: PM.check_mode)
    (e: exp t c a { XC.causal e })
    : Lemma (ensures check_invariant mode [] e)
      (decreases e) =
    let tx = SX.system_of_exp e in
    let rows: list (row c) = [] in
    match e with
    | XBase _ -> ()

    | XApps e1 ->
      check_apps_init mode e1 (fun r () -> r);
      ()

    | XFby v1 e2 ->
      check_init mode e2

    | XMu e1 ->
      check_init mode e1;
      ()

    | XLet b e1 e2 ->
      check_init mode e1;
      check_init mode e2;
      ()

    | XCheck _ e1 ->
      check_init mode e1

    | XContract ps er eg eb ->
      check_init mode er;
      check_init mode eg;
      ()

and check_apps_init
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (mode: PM.check_mode)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    : Lemma (ensures
        check_apps_invariant mode [] e)
      (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let f' = SX.system_of_exp_apps_distr f in
    check_apps_init mode e1 f';
    check_init mode e2;
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


let rec inputs_with_oracles
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  : list (row c & SB.option_type_sem (SX.oracle_of_exp e)) =
  match rows with
  | [] -> []
  | i :: rows' ->
    let o = SXP.step_oracle rows e in
    let ios = inputs_with_oracles rows' e in
    (i, o) :: ios

let rec inputs_with_oracles_contract_definition
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (r: exp t       c  t.propty { XC.causal r })
  (g: exp t (a :: c) t.propty { XC.causal g })
  (b: exp t       c         a { XC.causal b })
  : list (row c & SB.option_type_sem (SX.oracle_of_contract_definition r g b)) =
  match rows with
  | [] -> []
  | i :: rows' ->
    let vs = XC.lemma_bigsteps_total_vs rows b in
    let o = SB.type_join_tup
      (SXP.step_oracle rows r)
      (SB.type_join_tup
        (SXP.step_oracle (CR.extend1 vs rows) g)
        (SXP.step_oracle rows b))
    in
    let ios = inputs_with_oracles_contract_definition rows' r g b in
    (i, o) :: ios


let rec system_holds_prefix
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  : prop =
  match rows with
  | [] -> True
  | hd :: tl ->
    SI.system_holds (SX.system_of_exp e) (inputs_with_oracles rows e) /\
    system_holds_prefix tl e

let rec system_holds_prefix_of_all
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  : Lemma
    (requires (
      SI.system_holds_all (SX.system_of_exp e)
    ))
    (ensures (
      system_holds_prefix rows e
    )) =
  match rows with
  | [] -> ()
  | hd :: tl ->
    system_holds_prefix_of_all tl e

