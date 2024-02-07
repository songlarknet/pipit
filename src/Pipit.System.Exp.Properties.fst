(* Proofs related to abstract transition systems (Section 4) *)
module Pipit.System.Exp.Properties

open Pipit.Prim.Table
open Pipit.Exp.Base

module Table = Pipit.Prim.Table

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

module SB = Pipit.System.Base
module SX = Pipit.System.Exp

module X  = Pipit.Exp
module XB = Pipit.Exp.Bigstep
module XC = Pipit.Exp.Causality

module List = FStar.List.Tot

module T    = FStar.Tactics

#push-options "--split_queries always"

(*
   The invariant describes the transition system's state after it has been fed with all of `rows` as inputs.
*)
let rec system_of_exp_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a { XC.causal e })
  (s: SB.option_type_sem (SX.state_of_exp e)):
    Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> system_of_exp_apps_invariant rows e1 s

  | XFby v1 e2 ->
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
    (match rows with
    | [] -> SB.type_join_fst s == v1
    | _ :: _ ->
      let v: t.ty_sem a = XC.lemma_bigstep_total_v rows e2 in
      SB.type_join_fst s == v) /\
    system_of_exp_invariant rows e2 (SB.type_join_snd s)

  | XMu e1 ->
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows e) rows) e1 s

  | XLet b e1 e2 ->
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    system_of_exp_invariant rows e1 (SB.type_join_fst s) /\
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows e1) rows) e2 (SB.type_join_snd s)

  | XCheck _ e1 ->
    let s: SB.option_type_sem (SX.state_of_exp e1) = s in
    system_of_exp_invariant rows e1 s

  | XContract _ er eg eb ->
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in
    system_of_exp_invariant rows  er (SB.type_join_fst s) /\
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows eb) rows) eg (SB.type_join_snd s)

and system_of_exp_apps_invariant
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e })
  (s: SB.option_type_sem (SX.state_of_exp_apps e)):
    Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 ->
    assert_norm (SX.state_of_exp_apps (XApp e1 e2) == SB.type_join(SX.state_of_exp e2) (SX.state_of_exp_apps e1));
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in
    system_of_exp_apps_invariant rows e1 (SB.type_join_snd s) /\
    system_of_exp_invariant rows e2 (SB.type_join_fst s)

let system_of_contract_invariant
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (r: exp t       c  t.propty { XC.causal r })
  (g: exp t (a :: c) t.propty { XC.causal g })
  (b: exp t       c         a { XC.causal b })
  (s: SB.option_type_sem (SX.state_of_contract_definition r g b))
  : prop =
  let s: SB.option_type_sem
    (SB.type_join
      (SX.state_of_exp r)
      (SB.type_join
        (SX.state_of_exp g)
        (SX.state_of_exp b)))
    = s in
  let vs = XC.lemma_bigsteps_total_vs rows b in
  let sr = SB.type_join_fst s in
  let sg = SB.type_join_fst (SB.type_join_snd s) in
  let sb = SB.type_join_snd (SB.type_join_snd s) in
  system_of_exp_invariant rows r sr /\
  system_of_exp_invariant (CR.extend1 vs rows) g sg /\
  system_of_exp_invariant rows b sb

let lemma_system_of_exp_apps_init_XApp
  (#t: table) (#c: context t) (#arg: t.ty) (#resfun: funty t.ty) (#res #inp: Type0)
  (e1: exp_apps t c (FTFun arg resfun) { XC.causal_apps e1 })
  (e2: exp t c arg { XC.causal e2 })
  (f: funty_sem t.ty_sem resfun -> inp -> res)
  : Lemma (ensures
      (SX.system_of_exp_apps (XApp e1 e2) f).init ==
      SB.type_join_tup (SX.system_of_exp e2).init (SX.system_of_exp_apps e1 (SX.system_of_exp_apps_distr f)).init)
    =
  assert ((SX.system_of_exp_apps (XApp e1 e2) f).init ==
        SB.type_join_tup (SX.system_of_exp e2).init (SX.system_of_exp_apps e1 (SX.system_of_exp_apps_distr f)).init)
        by
    (FStar.Tactics.norm [delta_only [`%SX.system_of_exp_apps]; zeta; primops; iota; nbe ];
    FStar.Tactics.trefl ());
  ()

let rec invariant_init
  (#t: table) (#c: context t) (#a: t.ty)
  (e: exp t c a { XC.causal e })
  : Lemma (ensures
      system_of_exp_invariant [] e (SX.system_of_exp e).init)
    (decreases e) =
  let tx = SX.system_of_exp e in
  let rows: list (row c) = [] in
  match e with
  | XBase _ -> ()

  | XApps e1 ->
    step_apps_invariant_init e1 (fun r () -> r);
    let t' = SB.system_with_input (fun r -> ((), r)) (SX.system_of_exp_apps e1 (fun r () -> r)) in
    assert (SX.system_of_exp (XApps e1) == t')
      by (T.norm [delta; nbe; primops; iota; zeta];
          T.trefl ());
    ()

  | XFby v1 e2 ->
    invariant_init e2

  | XMu e1 ->
    invariant_init e1;
    ()

  | XLet b e1 e2 ->
    invariant_init e1;
    invariant_init e2;
    ()

  | XCheck _ e1 ->
    invariant_init e1

  | XContract ps er eg eb ->
    invariant_init er;
    invariant_init eg;
    ()

and step_apps_invariant_init
  (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
  (e: exp_apps t c a { XC.causal_apps e })
  (f: funty_sem t.ty_sem a -> inp -> res)
  : Lemma (ensures
      system_of_exp_apps_invariant [] e (SX.system_of_exp_apps e f).init)
    (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let f' = SX.system_of_exp_apps_distr f in
    step_apps_invariant_init e1 f';
    invariant_init e2;
    lemma_system_of_exp_apps_init_XApp e1 e2 f;
    ()


let rec step_oracle
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp t c a { XC.causal e })
  : Tot (SB.option_type_sem (SX.oracle_of_exp e)) (decreases e) =
  match e with
  | XBase _ -> ()

  | XApps e1 ->
    step_apps_oracle rows e1

  | XFby v1 e2 ->
    step_oracle rows e2

  | XMu e1 ->
    let vs = XC.lemma_bigsteps_total_vs rows (XMu e1) in
    let rows' = CR.extend1 vs rows in

    let orcl1 = step_oracle rows' e1 in
    SB.type_join_tup #(Some (t.ty_sem a)) #(SX.oracle_of_exp e1) (List.hd vs) orcl1

  | XLet b e1 e2 ->
    let vlefts = XC.lemma_bigsteps_total_vs rows e1 in
    let rows' = CR.extend1 vlefts rows in

    let orcl1 = step_oracle rows  e1 in
    let orcl2 = step_oracle rows' e2 in
    SB.type_join_tup orcl1 orcl2

  | XCheck _ e1 ->
    step_oracle rows e1

  | XContract ps er eg eb ->
    let vs = XC.lemma_bigsteps_total_vs rows eb in
    let rows' = CR.extend1 vs rows in

    let or = step_oracle rows  er in
    let og = step_oracle rows' eg in
    SB.type_join_tup #(Some (t.ty_sem a)) (List.hd vs) (SB.type_join_tup or og)

and step_apps_oracle
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c) { Cons? rows })
  (e: exp_apps t c a { XC.causal_apps e })
  : Tot (SB.option_type_sem (SX.oracle_of_exp_apps e)) (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let orcl2 = step_oracle      rows e2 in
    let orcl1 = step_apps_oracle rows e1 in
    SB.type_join_tup #(SX.oracle_of_exp e2) #(SX.oracle_of_exp_apps e1) orcl2 orcl1

let rec invariant_step
  (#t: table) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (row1: row c)
  (e: exp t c a { XC.causal e })
  (s: SB.option_type_sem (SX.state_of_exp e) { system_of_exp_invariant rows e s })
  : Lemma (ensures (
      let stp = (SX.system_of_exp e).step row1 (step_oracle (row1 :: rows) e) s in
      stp.v == (XC.lemma_bigstep_total_v (row1 :: rows) e) /\ system_of_exp_invariant (row1 :: rows) e stp.s
  )) (decreases e) =
  match e with
  | XBase _ -> ()

  | XApps e1 ->
    invariant_step_apps rows row1 e1 SX.system_of_exp_apps_const () s

  | XFby v1 e2 ->
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (SX.state_of_exp e2)) = s in
    invariant_step rows row1 e2 (SB.type_join_snd s);
    ()

  | XMu e1 ->
    let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) (XMu e1) in
    let rows' = CR.extend1 vs rows in
    let row1' = CR.cons v row1 in
    invariant_step rows' row1' e1 s;
    ()

  | XLet b e1 e2 ->
    let vleft :: vlefts = XC.lemma_bigsteps_total_vs (row1 :: rows) e1 in
    let rows' = CR.extend1 vlefts rows in
    let row1' = CR.cons vleft row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e1) (SX.state_of_exp e2)) = s in
    invariant_step rows  row1  e1 (SB.type_join_fst s);
    invariant_step rows' row1' e2 (SB.type_join_snd s);
    ()

  | XCheck _ e1 ->
    invariant_step rows row1 e1 s

  | XContract ps er eg eb ->
    let v :: vs = XC.lemma_bigsteps_total_vs (row1 :: rows) eb in
    let rows' = CR.extend1 vs rows in
    let row1' = CR.cons v row1 in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp er) (SX.state_of_exp eg)) = s in
    invariant_step rows  row1  er (SB.type_join_fst s);
    invariant_step rows' row1' eg (SB.type_join_snd s);
    ()

and invariant_step_apps
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (rows: list (row c))
    (row1: row c)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    (inp0: inp)
    (s: SB.option_type_sem (SX.state_of_exp_apps e) { system_of_exp_apps_invariant rows e s })
    : Lemma (ensures (
      let stp = (SX.system_of_exp_apps e f).step (inp0, row1) (step_apps_oracle (row1 :: rows) e) s in
      stp.v == f (dfst (XC.lemma_bigstep_apps_total (row1 :: rows) e)) inp0 /\ system_of_exp_apps_invariant (row1 :: rows) e stp.s))
    (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let v2 = XC.lemma_bigstep_total_v (row1 :: rows) e2 in
    let f' = SX.system_of_exp_apps_distr f in
    let s: SB.option_type_sem (SB.type_join (SX.state_of_exp e2) (SX.state_of_exp_apps e1)) = s in
    invariant_step rows row1 e2 (SB.type_join_fst s);
    invariant_step_apps rows row1 e1 f' (v2, inp0) (SB.type_join_snd s);
    assert (
      let stp = (SX.system_of_exp_apps e f).step (inp0, row1) (step_apps_oracle (row1 :: rows) e) s in
      stp.v == f (dfst (XC.lemma_bigstep_apps_total (row1 :: rows) e)) inp0);
    assert (
      let stp = (SX.system_of_exp_apps e f).step (inp0, row1) (step_apps_oracle (row1 :: rows) e) s in
      system_of_exp_apps_invariant (row1 :: rows) e stp.s);
    ()


let rec system_invariant_many
    (#t: table) (#c: context t) (#a: t.ty)
    (inputs: list (row c))
    (e: exp t c a { XC.causal e })
    : Tot (
        state:   SB.option_type_sem (SX.state_of_exp e) { system_of_exp_invariant inputs e state } &
        oracles: list (SB.option_type_sem (SX.oracle_of_exp e)) { List.length oracles == List.length inputs } &
        results: list (t.ty_sem a) { List.length results == List.length inputs } &
        XB.bigsteps inputs e results &
        squash (
          SB.system_steps (SX.system_of_exp e) inputs oracles == (state, results)
        )) =
    let t = SX.system_of_exp e in
    match inputs with
    | [] ->
      invariant_init e;
      assert (SB.system_steps (SX.system_of_exp e) inputs [] == (t.init, []));
      (| t.init, [], [], XB.BSs0 e, () |)
    | i :: inputs' ->
      let (| s, oracles, results, hBSs, prf |) = system_invariant_many inputs' e in
      let (| r, hBS |) = XC.lemma_bigstep_total (i :: inputs') e in
      let o = step_oracle (i :: inputs') e in
      invariant_step inputs' i e s;
      let stp = t.step i o s in
      assert (SB.system_steps (SX.system_of_exp e)       inputs'        oracles  == (    s,      results));
      assert (SB.system_steps (SX.system_of_exp e) (i :: inputs') (o :: oracles) == (stp.s, r :: results));
      assert (SB.system_steps (SX.system_of_exp e)       inputs   (o :: oracles) == (stp.s, r :: results));
      let hBSs': XB.bigsteps (i :: inputs') e (r :: results) = XB.BSsS _ e _ _ _ hBSs hBS in
      (| stp.s, o :: oracles, r :: results, hBSs', () |)


(* Section 4, Theorem 4, translation-abstraction *)
let system_translation_abstraction
    (#t: table) (#c: context t) (#a: t.ty)
    (inputs: list (row c))
    (e: exp t c a { XC.causal e })
    (results: list (t.ty_sem a) { List.length results == List.length inputs })
    (hBSs: XB.bigsteps inputs e results)
    : Tot (oracles: list (SB.option_type_sem (SX.oracle_of_exp e)) {
          List.length oracles == List.length inputs /\
          snd (SB.system_steps (SX.system_of_exp e) inputs oracles) == results
      }) =
  let (| s, oracles, results', hBSs', prf |) = system_invariant_many inputs e in
  XB.bigsteps_proof_equivalence hBSs hBSs';
  oracles
