(* Translation to executable transition system proof *)
module Pipit.System.Exec.Exp.Properties

open Pipit.Prim.Table
open Pipit.Exp.Base

module Table = Pipit.Prim.Table

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row

module SB = Pipit.System.Base
module SX = Pipit.System.Exp

module E  = Pipit.System.Exec
module EX = Pipit.System.Exec.Exp

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
  (s: SB.option_type_sem (EX.estate_of_exp e)):
    Tot prop (decreases e) =
  match e with
  | XBase _ -> True
  | XApps e1 -> system_of_exp_apps_invariant rows e1 s

  | XFby v1 e2 ->
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (EX.estate_of_exp e2)) = s in
    (match rows with
    | [] -> SB.type_join_fst s == v1
    | _ :: _ -> XB.bigstep rows e2 (SB.type_join_fst s)) /\ system_of_exp_invariant rows e2 (SB.type_join_snd s)

  | XMu e1 ->
    // let s: SB.option_type_sem (EX.estate_of_exp e1) = coerce_eq () s in
    system_of_exp_invariant (CR.zip2_cons (XC.lemma_bigsteps_total_vs rows e) rows) e1 s

  | XLet b e1 e2 ->
    let s: SB.option_type_sem (SB.type_join (EX.estate_of_exp e1) (EX.estate_of_exp e2)) = s in
    system_of_exp_invariant rows e1 (SB.type_join_fst s) /\
    system_of_exp_invariant (CR.zip2_cons (XC.lemma_bigsteps_total_vs rows e1) rows) e2 (SB.type_join_snd s)

  | XCheck _ e1 ->
    // We don't execute checks for extraction
    True

  | XContract _ _ _ eb ->
    // This is the main difference from Pipit.System.Exp.Properties: we just use the implementation body rather than contract rely/guar
    system_of_exp_invariant rows  eb s

and system_of_exp_apps_invariant
  (#t: table) (#c: context t) (#a: funty t.ty)
  (rows: list (row c))
  (e: exp_apps t c a { XC.causal_apps e })
  (s: SB.option_type_sem (EX.estate_of_exp_apps e)):
    Tot prop (decreases e) =
  match e with
  | XPrim _ -> True
  | XApp e1 e2 ->
    assert_norm (EX.estate_of_exp_apps (XApp e1 e2) == SB.type_join(EX.estate_of_exp e2) (EX.estate_of_exp_apps e1));
    let s: SB.option_type_sem (SB.type_join (EX.estate_of_exp e2) (EX.estate_of_exp_apps e1)) = s in
    system_of_exp_apps_invariant rows e1 (SB.type_join_snd s) /\
    system_of_exp_invariant rows e2 (SB.type_join_fst s)



let tac_simp_refl () =
  T.norm [delta; nbe; primops; iota; zeta];
  T.trefl ()

let rec step_invariant_init
    (#t: table) (#c: context t) (#a: t.ty)
    (e: exp t c a { XC.causal e })
    : Lemma (ensures
        system_of_exp_invariant [] e (EX.esystem_of_exp e).init)
      (decreases e) =
    let tx = EX.esystem_of_exp e in
    let rows: list (row c) = [] in
    match e with
    | XBase _ -> ()

    | XApps e1 ->
      step_apps_invariant_init e1 (fun r () -> r);
      // TODO norm etc
      // norm_spec [delta; nbe; primops; iota; zeta] (EX.esystem_of_exp (XApps e1));
      // let t' = SB.system_with_input (fun r -> ((), r)) (EX.esystem_of_exp_apps e1 (fun r () -> r)) in
      // assert (EX.esystem_of_exp (XApps e1) == t')
        // by (tac_simp_refl ());
      admit () // ASSUME

    | XFby v1 e2 ->
      step_invariant_init e2

    | XMu e1 ->
      step_invariant_init e1;
      ()

    | XLet b e1 e2 ->
      step_invariant_init e1;
      step_invariant_init e2;
      ()

    | XCheck _ e1 ->
      ()

    | XContract ps er eg eb ->
      step_invariant_init eb

and step_apps_invariant_init
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (e: exp_apps t c a { XC.causal_apps e })
    (f: funty_sem t.ty_sem a -> inp -> res)
    : Lemma (ensures
        system_of_exp_apps_invariant [] e (EX.esystem_of_exp_apps e f).init)
      (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let f' = SX.system_of_exp_apps_distr f in
    step_apps_invariant_init e1 f';
    step_invariant_init e2;
    ()


let rec step_invariant_step
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (row1: row c)
    (e: exp t c a { XC.causal e })
    (v: t.ty_sem a)
    (hBS: XB.bigstep (row1 :: rows) e v)
    (s: SB.option_type_sem (EX.estate_of_exp e) { system_of_exp_invariant rows e s })
    : Lemma (ensures
        (let (s', v') = (EX.esystem_of_exp e).step row1 s in
        v' == v /\ system_of_exp_invariant (row1 :: rows) e s'))
      (decreases e) =
    match e with
    | XBase _ -> ()

    | XApps e1 ->
      let XB.BSApps _ _ _ hBSa = hBS in
      step_apps_invariant_step rows row1 e1 v hBSa SX.system_of_exp_apps_const () s

    | XFby v1 e2 ->
      let (| v2, hBS2 |) = XC.lemma_bigstep_total (row1 :: rows) e2 in
      let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem a)) (EX.estate_of_exp e2)) = s in
      step_invariant_step rows row1 e2 v2 hBS2 (SB.type_join_snd s);
      (match hBS with
      | XB.BSFby1 _ _ _ ->
        ()
      | XB.BSFbyS _ _ _ _ _ hBS' ->
      //XXX don't need squash
        XB.bigstep_deterministic_squash rows e2 v (SB.type_join_fst s);
        ())

    | XMu e1 ->
      let (| vs', hBSMus'|) = XC.lemma_bigsteps_total (row1 :: rows) (XMu e1) in
      let XB.BSsS _ _ vs _ v' hBSMus hBSMu = hBSMus' in
      XB.bigstep_deterministic hBS hBSMu;
      let rows' = CR.zip2_cons vs rows in

      let bottom = t.val_default a in
      let t1 = EX.esystem_of_exp e1 in
      let t' = E.esystem_mu_causal bottom (fun i v -> (v, i)) t1 in

      let (s_scrap, v0) = t1.step (bottom, row1) s in
      let (s1', v_scrap) = t1.step (v0, row1) s in


      let (| v0x, hBSX |) = XC.lemma_bigstep_total (CR.cons bottom row1 :: rows') e1 in

      let hBSMuBot: XB.bigstep (row1 :: rows) (XMu e1) v0x = XC.lemma_bigstep_substitute_intros_XMu rows e1 vs row1 v0x bottom hBSMus hBSX in
      XB.bigstep_deterministic hBSMuBot hBSMu;

      assert (v0x == v);

      step_invariant_step rows' (CR.cons bottom row1) e1 v hBSX s;

      let s: SB.option_type_sem (EX.estate_of_exp e1) = s in
      assert (system_of_exp_invariant rows' e1 s);

      let hBS1: XB.bigstep (CR.cons v row1 :: rows') e1 v = XC.lemma_bigstep_substitute_elim_XMu (row1 :: rows) e1 (v :: vs) hBSMus' in

      step_invariant_step rows' (CR.cons v row1) e1 v hBS1 s;
      let stp = (EX.esystem_of_exp (XMu e1)).step row1 s in
      assert (system_of_exp_invariant (row1 :: rows) (XMu e1) (fst stp));
      ()

    | XLet b e1 e2 ->
      let (| vlefts', hBS1s' |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
      let XB.BSsS _ _ vlefts _ vleft hBS1s hBS1 = hBS1s' in
      let rows' = CR.zip2_cons vlefts rows in
      let row1' = CR.cons vleft row1 in
      let s: SB.option_type_sem (SB.type_join (EX.estate_of_exp e1) (EX.estate_of_exp e2)) = s in
      assert (system_of_exp_invariant rows  e1 (SB.type_join_fst s));
      assert (system_of_exp_invariant rows' e2 (SB.type_join_snd s));

      let hBS2 = XC.lemma_bigstep_substitute_elim_XLet (row1 :: rows) e1 vlefts' hBS1s' e2 v hBS in

      step_invariant_step rows  row1  e1 vleft hBS1 (SB.type_join_fst s);
      step_invariant_step rows' row1' e2 v     hBS2 (SB.type_join_snd s)

    | XCheck _ e1 ->
      ()

    | XContract ps er eg eb ->
      let XB.BSContract _ _ _ _ _ _ hBSb' = hBS in
      step_invariant_step rows row1 eb v hBSb' s

and step_apps_invariant_step
    (#t: table) (#c: context t) (#a: funty t.ty) (#res #inp: Type0)
    (rows: list (row c))
    (row1: row c)
    (e: exp_apps t c a { XC.causal_apps e })
    (v: funty_sem t.ty_sem a)
    (hBS: XB.bigstep_apps (row1 :: rows) e v)
    (f: funty_sem t.ty_sem a -> inp -> res)
    (inp0: inp)
    (s: SB.option_type_sem (EX.estate_of_exp_apps e) { system_of_exp_apps_invariant rows e s })
    : Lemma (ensures (
        let (s', v') = (EX.esystem_of_exp_apps e f).step (inp0, row1) s in
        v' == f v inp0 /\
        system_of_exp_apps_invariant (row1 :: rows) e s'))
      (decreases e) =
  match e with
  | XPrim _ -> ()
  | XApp e1 e2 ->
    let XB.BSApp _ _ _ v1 v2 hBS1 hBS2 = hBS in
    let f' = SX.system_of_exp_apps_distr f in
    let s: SB.option_type_sem (SB.type_join (EX.estate_of_exp e2) (EX.estate_of_exp_apps e1)) = s in
    step_invariant_step      rows row1 e2 v2 hBS2 (SB.type_join_fst s);
    step_apps_invariant_step rows row1 e1 v1 hBS1 f' (v2, inp0) (SB.type_join_snd s)

// TODO: state high-level lemma: for any inputs, iterated steps results in the same as bigstep