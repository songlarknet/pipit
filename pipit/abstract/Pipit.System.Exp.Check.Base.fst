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
module XBind = Pipit.Exp.Binding

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

  | XMufby acc seed f g ->
    // Property-check invariant for the fused loop.  `f` checks on the
    // operational accumulator history `accsys = seed fby g(mres)`, and `g` on
    // the output history `mres = mufby_desugar seed f g` (mirrors the system
    // invariant Pipit.System.Exp.Properties.system_of_exp_invariant).
    let mres = XBind.mufby_desugar seed f g in
    let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
    XC.lemma_causal_XMufby seed f g;
    check_invariant mode (CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows) f /\
    check_invariant mode (CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows) g

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

    | XMufby acc seed f g ->
      let mres = XBind.mufby_desugar seed f g in
      let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
      XC.lemma_causal_XMufby seed f g;
      check_init mode f;
      check_init mode g;
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


(* Decomposition of the fused-loop step into its f- and g- sub-steps.  The
   XMufby system runs f ONCE on the (delayed) accumulator history `accsys` and g
   ONCE on the output history `mres`; the loop is causal-by-construction, so the
   output is f's computed value (no res-oracle, no per-step fixpoint assumption).
   This helper exposes the f/g sub-invariants and history bridges (so
   `eval_step`/`check_invariant` on f/g line up), the output equality
   `stpf.v == v`, and the chck decomposition of the composite step (= f's checks
   joined with g's checks, nothing extra). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 300"
let lemma_eval_step_XMufby
    (#t: table) (#c: context t) (#acc #a: t.ty)
    (seed: t.ty_sem acc)
    (f: exp t (acc :: c) a { XC.causal f })
    (g: exp t (a :: c) acc { XC.causal g })
    (rows: list (row c))
    (row1: row c)
    (s: SB.option_type_sem (SX.state_of_exp (XMufby acc seed f g))
      { SXP.system_of_exp_invariant rows (XMufby acc seed f g) s })
    : Lemma
      (requires (
        XC.causal (XBind.mufby_desugar seed f g) /\
        XC.causal (XFby seed (XBind.subst1 g (XBind.mufby_desugar seed f g)))))
      (ensures (
      let e = XMufby acc seed f g in
      let mres = XBind.mufby_desugar seed f g in
      let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
      let reg_acc = SB.type_join_fst #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) s in
      let inner = SB.type_join_snd #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) s in
      let sf = SB.type_join_fst #(SX.state_of_exp f) #(SX.state_of_exp g) inner in
      let sg = SB.type_join_snd #(SX.state_of_exp f) #(SX.state_of_exp g) inner in
      let rows_f = CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows in
      let rows_g = CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows in
      let v = XC.lemma_bigstep_total_v (row1 :: rows) e in
      SXP.system_of_exp_invariant rows_f f sf /\
      SXP.system_of_exp_invariant rows_g g sg /\
      CR.extend1 (XC.lemma_bigsteps_total_vs (row1 :: rows) accsys) (row1 :: rows) == CR.cons reg_acc row1 :: rows_f /\
      CR.extend1 (XC.lemma_bigsteps_total_vs (row1 :: rows) mres) (row1 :: rows) == CR.cons v row1 :: rows_g /\
      (let stpf = (SX.system_of_exp f).step (CR.cons reg_acc row1) (SXP.step_oracle (CR.cons reg_acc row1 :: rows_f) f) sf in
       let stpg = (SX.system_of_exp g).step (CR.cons v row1) (SXP.step_oracle (CR.cons v row1 :: rows_g) g) sg in
       let stp  = (SX.system_of_exp e).step row1 (SXP.step_oracle (row1 :: rows) e) s in
       stpf.v == v /\
       stp.chck == stpf.chck `SB.checks_join` stpg.chck)))
    =
    let e = XMufby acc seed f g in
    let mres = XBind.mufby_desugar seed f g in
    let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
    assert_norm (XC.causal (XMufby acc seed f g) == (XC.causal f && XC.causal g));
    XC.lemma_causal_mufby_desugar seed f g;
    XC.lemma_causal_subst g 0 mres;
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem acc)) (SB.type_join (SX.state_of_exp f) (SX.state_of_exp g))) = s in
    let reg_acc = SB.type_join_fst s in
    let inner = SB.type_join_snd s in
    let sf = SB.type_join_fst inner in
    let sg = SB.type_join_snd inner in
    // current-state invariant conjuncts
    assert (SXP.system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows) f sf);
    assert (SXP.system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows) g sg);
    assert (match rows with
            | [] -> reg_acc == seed
            | _ :: _ -> XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc);

    // (A) The loop output equals the desugar output; via desugar-output the
    //     f-value on the accumulator history equals that output.
    let (| v, hBS |) = XC.lemma_bigstep_total (row1 :: rows) e in
    let hBS_mres : XB.bigstep (row1 :: rows) mres v =
      (match hBS with | XB.BSMufby _ _ _ _ _ h -> h) in
    let hBS_subst : XB.bigstep (row1 :: rows) (XBind.subst1 f accsys) v =
      XC.lemma_bigstep_mufby_desugar_output (row1 :: rows) seed f g v hBS_mres in

    // (B) The accumulator value stream; its head equals the register value.
    let (| avs, hBSaccsys' |) = XC.lemma_bigsteps_total (row1 :: rows) accsys in
    let XB.BSsS _ _ avs_tl _ av_hd hBSaccsys_tl hBSaccsys_head = hBSaccsys' in
    (match rows with
     | [] ->
       assert (reg_acc == seed);
       (match hBSaccsys_head with | XB.BSFby1 _ _ _ -> ())
     | _ :: _ ->
       assert (XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc);
       (match hBSaccsys_head with
        | XB.BSFbyS _ _ _ _ _ hprev ->
          introduce exists (h: XB.bigstep rows (XBind.subst1 g mres) av_hd). True
            with hprev and ();
          XB.bigstep_deterministic_squash rows (XBind.subst1 g mres) av_hd reg_acc));
    assert (av_hd == reg_acc);

    let rows_f = CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows in
    let rows_g = CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows in
    assert (CR.extend1 avs (row1 :: rows) == CR.cons reg_acc row1 :: rows_f);

    // (C) f's bigstep on the accsys-extended history produces v (fixpoint).
    let hBS_f0 : XB.bigstep (CR.extend1 avs (row1 :: rows)) f v =
      XC.lemma_bigstep_substitute_elim 0 (row1 :: rows) accsys avs f v hBSaccsys' hBS_subst in
    let hBS_f : XB.bigstep (CR.cons reg_acc row1 :: rows_f) f v = hBS_f0 in
    XB.bigstep_deterministic_squash (CR.cons reg_acc row1 :: rows_f) f v
      (XC.lemma_bigstep_total_v (CR.cons reg_acc row1 :: rows_f) f);

    // (D) The mres output stream; head == v.
    let (| mvs, hBSmres' |) = XC.lemma_bigsteps_total (row1 :: rows) mres in
    let XB.BSsS _ _ mvs_tl _ mv_hd hBSmres_tl hBSmres_head = hBSmres' in
    XB.bigstep_deterministic hBS_mres hBSmres_head;
    assert (CR.extend1 mvs (row1 :: rows) == CR.cons v row1 :: rows_g);

    // (E) eval-step f/g and compose the chck.  The oracle components of the
    //     composite step_oracle are exactly step_oracle on the f/g histories.
    let stpf = eval_step rows_f (CR.cons reg_acc row1) f sf in
    let stpg = eval_step rows_g (CR.cons v row1) g sg in
    assert (stpf.v == v);

    let o_all = SXP.step_oracle (row1 :: rows) e in
    assert (SB.type_join_fst #(SX.oracle_of_exp f) #(SX.oracle_of_exp g) o_all
              == SXP.step_oracle (CR.cons reg_acc row1 :: rows_f) f);
    assert (SB.type_join_snd #(SX.oracle_of_exp f) #(SX.oracle_of_exp g) o_all
              == SXP.step_oracle (CR.cons v row1 :: rows_g) g);
    let stp = eval_step rows row1 e s in
    assert (stp.chck == stpf.chck `SB.checks_join` stpg.chck);
    ()
#pop-options


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

