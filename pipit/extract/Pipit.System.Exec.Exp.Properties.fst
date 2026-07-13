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
module XBind = Pipit.Exp.Binding

module List = FStar.List.Tot

module T    = FStar.Tactics

#set-options "--split_queries always"

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
    | _ :: _ -> XB.bigstep_prop rows e2 (SB.type_join_fst s)) /\ system_of_exp_invariant rows e2 (SB.type_join_snd s)

  | XMu e1 ->
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows e) rows) e1 s

  | XMufby acc seed f g ->
    // esystem_mufby state = (register acc, (f-state, g-state)).
    // The register holds the accumulator used next; f runs on the *operational*
    // accumulator stream `accsys = seed fby g(mres)` (exactly what the executable
    // step feeds f), and g runs on the output stream `mufby_desugar`.
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem acc)) (SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g))) = s in
    let reg_acc = SB.type_join_fst s in
    let inner = SB.type_join_snd s in
    let sf = SB.type_join_fst inner in
    let sg = SB.type_join_snd inner in
    let mres = XBind.mufby_desugar seed f g in
    let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
    XC.lemma_causal_mufby_desugar seed f g;
    assert_norm (XC.causal (XMufby acc seed f g) == (XC.causal f && XC.causal g));
    XC.lemma_causal_subst g 0 mres;
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows) f sf /\
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows) g sg /\
    (match rows with
     | [] -> reg_acc == seed
     | _ :: _ -> XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc)

  | XLet b e1 e2 ->
    let s: SB.option_type_sem (SB.type_join (EX.estate_of_exp e1) (EX.estate_of_exp e2)) = s in
    system_of_exp_invariant rows e1 (SB.type_join_fst s) /\
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows e1) rows) e2 (SB.type_join_snd s)

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
      let f0: funty_sem t.ty_sem (FTVal a) -> unit -> funty_sem t.ty_sem (FTVal a) = SX.system_of_exp_apps_const in
      step_apps_invariant_init e1 f0;
      assert_norm ((EX.esystem_of_exp (XApps e1)).init == (EX.esystem_of_exp_apps e1 f0).init);
      ()

    | XFby v1 e2 ->
      step_invariant_init e2

    | XMu e1 ->
      step_invariant_init e1;
      ()

    | XMufby acc seed f g ->
      assert_norm (XC.causal (XMufby acc seed f g) == (XC.causal f && XC.causal g));
      step_invariant_init f;
      step_invariant_init g;
      XC.lemma_causal_mufby_desugar seed f g;
      XC.lemma_causal_subst g 0 (XBind.mufby_desugar seed f g);
      // Reduce the fused-loop initial state to its `type_join_tup` structure so
      // SMT can discharge the register/sub-state projections in the invariant.
      assert ((EX.esystem_of_exp (XMufby acc seed f g)).init ==
        SB.type_join_tup #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) seed
          (SB.type_join_tup #(EX.estate_of_exp f) #(EX.estate_of_exp g) (EX.esystem_of_exp f).init (EX.esystem_of_exp g).init))
        by (T.norm [delta_only [`%EX.esystem_of_exp; `%E.esystem_mufby]; zeta; primops; iota; nbe]; T.trefl ());
      let inner0 : SB.option_type_sem (SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) =
        SB.type_join_tup #(EX.estate_of_exp f) #(EX.estate_of_exp g) (EX.esystem_of_exp f).init (EX.esystem_of_exp g).init in
      let s0 : SB.option_type_sem (EX.estate_of_exp (XMufby acc seed f g)) =
        SB.type_join_tup #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) seed inner0 in
      // Each projection needs only a single Some/None case split.
      assert (SB.type_join_fst #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) s0 == seed);
      assert (SB.type_join_snd #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) s0 == inner0);
      assert (SB.type_join_fst #(EX.estate_of_exp f) #(EX.estate_of_exp g) inner0 == (EX.esystem_of_exp f).init);
      assert (SB.type_join_snd #(EX.estate_of_exp f) #(EX.estate_of_exp g) inner0 == (EX.esystem_of_exp g).init);
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


(* Congruence for the invariant under state equality.  Used to transfer the
   invariant, established on an explicitly-reconstructed state `s'`, to the
   operational step output `fst stp` (== s') without re-unfolding the invariant
   on the opaque step result. *)
let lemma_system_of_exp_invariant_cong
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (e: exp t c a { XC.causal e })
    (s1 s2: SB.option_type_sem (EX.estate_of_exp e))
    : Lemma (requires s1 == s2 /\ system_of_exp_invariant rows e s1)
        (ensures system_of_exp_invariant rows e s2) = ()

#push-options "--fuel 4 --ifuel 2 --z3rlimit 300"
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
      let rows' = CR.extend1 vs rows in

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

    | XMufby acc seed f g ->
      // Single-evaluation bisimulation for the fused loop.
      //
      // esystem_mufby.step reads reg_acc = type_join_fst s, runs f ONCE on
      // (reg_acc, row1) to get res, then g ONCE on (res, row1) to get the next
      // accumulator acc'; it outputs res and stores (acc', (sf', sg')).
      //
      // The f-side is now symmetric to the g-side because the invariant tracks
      // f's history against the *operational* accumulator stream
      // `accsys = seed fby g(mres)` -- exactly the register value fed to f.
      let mres = XBind.mufby_desugar seed f g in
      let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
      assert_norm (XC.causal (XMufby acc seed f g) == (XC.causal f && XC.causal g));
      XC.lemma_causal_mufby_desugar seed f g;
      XC.lemma_causal_subst g 0 mres;
      let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem acc)) (SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g))) = s in
      let reg_acc = SB.type_join_fst s in
      let inner = SB.type_join_snd s in
      let sf = SB.type_join_fst inner in
      let sg = SB.type_join_snd inner in
      // Expose the current-state invariant's conjuncts (sub-invariants for f/g
      // and the register fact) while the parameter refinement is fresh.
      assert (system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows) f sf);
      assert (system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows) g sg);
      assert (match rows with
              | [] -> reg_acc == seed
              | _ :: _ -> XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc);

      // (A) The fused-loop output is the desugar's output; unfolding one loop
      //     step exposes `f` applied to the operational accumulator `accsys`.
      let hBS_mres : XB.bigstep (row1 :: rows) mres v =
        (match hBS with | XB.BSMufby _ _ _ _ _ h -> h) in
      let hBS_subst : XB.bigstep (row1 :: rows) (XBind.subst1 f accsys) v =
        XC.lemma_bigstep_mufby_desugar_output (row1 :: rows) seed f g v hBS_mres in

      // (B) The accumulator value stream; its head equals the register value.
      let (| avs, hBSaccsys' |) = XC.lemma_bigsteps_total (row1 :: rows) accsys in
      let XB.BSsS _ _ avs_tl _ av_hd hBSaccsys_tl hBSaccsys_head = hBSaccsys' in
      // The register fact from the current-state invariant identifies av_hd (the
      // accumulator value of accsys = seed fby g(mres)) with reg_acc.
      (match rows with
       | [] ->
         // register invariant: reg_acc == seed; accsys value at [row1] is seed.
         assert (reg_acc == seed);
         (match hBSaccsys_head with | XB.BSFby1 _ _ _ -> ())
       | _ :: _ ->
         // register invariant: bigstep_prop rows (subst1 g mres) reg_acc.
         assert (XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc);
         (match hBSaccsys_head with
          | XB.BSFbyS _ _ _ _ _ hprev ->
            introduce exists (h: XB.bigstep rows (XBind.subst1 g mres) av_hd). True
              with hprev and ();
            XB.bigstep_deterministic_squash rows (XBind.subst1 g mres) av_hd reg_acc));
      assert (av_hd == reg_acc);

      // (C) f's bigstep on the accsys-extended history, producing v; recurse.
      let hBS_f0 : XB.bigstep (CR.extend1 avs (row1 :: rows)) f v =
        XC.lemma_bigstep_substitute_elim 0 (row1 :: rows) accsys avs f v hBSaccsys' hBS_subst in
      let rows_f = CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows in
      assert (CR.extend1 avs (row1 :: rows) == CR.cons reg_acc row1 :: rows_f);
      let hBS_f : XB.bigstep (CR.cons reg_acc row1 :: rows_f) f v = hBS_f0 in
      step_invariant_step rows_f (CR.cons reg_acc row1) f v hBS_f sf;

      // (D) g's next accumulator on the mres-extended history; recurse.
      let (| mvs, hBSmres' |) = XC.lemma_bigsteps_total (row1 :: rows) mres in
      let XB.BSsS _ _ mvs_tl _ mv_hd hBSmres_tl hBSmres_head = hBSmres' in
      XB.bigstep_deterministic hBS_mres hBSmres_head;
      assert (mv_hd == v);
      let rows_g = CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows in
      assert (CR.extend1 mvs (row1 :: rows) == CR.cons v row1 :: rows_g);
      let (| v_g, hBS_g0 |) = XC.lemma_bigstep_total (CR.extend1 mvs (row1 :: rows)) g in
      let hBS_g : XB.bigstep (CR.cons v row1 :: rows_g) g v_g = hBS_g0 in
      step_invariant_step rows_g (CR.cons v row1) g v_g hBS_g sg;

      // register fact for the new accumulator: bigstep_prop (subst1 g mres) v_g.
      let hBSreg : XB.bigstep (row1 :: rows) (XBind.subst1 g mres) v_g =
        XC.lemma_bigstep_substitute_intros 0 (row1 :: rows) mres mvs g v_g hBSmres' hBS_g0 in

      // (E) Reconstruct the new state `s' = (acc', (sf', sg'))` from the f/g
      //     sub-steps (each evaluated once) and prove the invariant on it.
      let (sf', res) = (EX.esystem_of_exp f).step (CR.cons reg_acc row1) sf in
      // res == v from the f recursion (input (reg_acc, row1) == CR.cons reg_acc row1).
      let (sg', acc') = (EX.esystem_of_exp g).step (CR.cons res row1) sg in
      // acc' == v_g from the g recursion (res == v).
      assert (acc' == v_g);
      let s' : SB.option_type_sem (EX.estate_of_exp (XMufby acc seed f g)) =
        SB.type_join_tup #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g))
          acc' (SB.type_join_tup #(EX.estate_of_exp f) #(EX.estate_of_exp g) sf' sg') in
      // single-level type_join projections of the new state
      assert (SB.type_join_fst #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) s' == acc');
      assert (SB.type_join_snd #(Some (t.ty_sem acc)) #(SB.type_join (EX.estate_of_exp f) (EX.estate_of_exp g)) s' == SB.type_join_tup sf' sg');
      assert (SB.type_join_fst #(EX.estate_of_exp f) #(EX.estate_of_exp g) (SB.type_join_tup sf' sg') == sf');
      assert (SB.type_join_snd #(EX.estate_of_exp f) #(EX.estate_of_exp g) (SB.type_join_tup sf' sg') == sg');
      // Bridge the recursion output histories to the new-state invariant's histories.
      assert (CR.extend1 (XC.lemma_bigsteps_total_vs (row1 :: rows) accsys) (row1 :: rows) == CR.cons reg_acc row1 :: rows_f);
      assert (CR.extend1 (XC.lemma_bigsteps_total_vs (row1 :: rows) mres) (row1 :: rows) == CR.cons v row1 :: rows_g);
      // register bigstep for the new accumulator acc' == v_g
      introduce exists (h: XB.bigstep (row1 :: rows) (XBind.subst1 g mres) acc'). True
        with hBSreg and ();
      assert (system_of_exp_invariant (row1 :: rows) (XMufby acc seed f g) s');
      // The operational step outputs (s', res): fst stp == s', snd stp == v.
      let stp = (EX.esystem_of_exp e).step row1 s in
      assert (fst stp == s');
      assert (snd stp == v);
      // Transfer the invariant to the step output by congruence (fst stp == s').
      lemma_system_of_exp_invariant_cong (row1 :: rows) e s' (fst stp);
      ()

    | XLet b e1 e2 ->
      let (| vlefts', hBS1s' |) = XC.lemma_bigsteps_total (row1 :: rows) e1 in
      let XB.BSsS _ _ vlefts _ vleft hBS1s hBS1 = hBS1s' in
      let rows' = CR.extend1 vlefts rows in
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
    assert_norm (EX.estate_of_exp_apps (XApp e1 e2) == SB.type_join (EX.estate_of_exp e2) (EX.estate_of_exp_apps e1));
    let s: SB.option_type_sem (SB.type_join (EX.estate_of_exp e2) (EX.estate_of_exp_apps e1)) = s in
    assert (system_of_exp_invariant rows e2 (SB.type_join_fst s));
    assert (system_of_exp_apps_invariant rows e1 (SB.type_join_snd s));
    step_invariant_step      rows row1 e2 v2 hBS2 (SB.type_join_fst s);
    step_apps_invariant_step rows row1 e1 v1 hBS1 f' (v2, inp0) (SB.type_join_snd s)

#pop-options

let rec system_invariant_many
    (#t: table) (#c: context t) (#a: t.ty)
    (inputs: list (row c))
    (e: exp t c a { XC.causal e })
    : Tot (
        state:   SB.option_type_sem (EX.estate_of_exp e) { system_of_exp_invariant inputs e state } &
        results: list (t.ty_sem a) { List.length results == List.length inputs } &
        XB.bigsteps inputs e results &
        squash (
          E.esystem_steps (EX.esystem_of_exp e) inputs == (state, results)
        )) =
    let t = EX.esystem_of_exp e in
    let (s',v) = E.esystem_steps (EX.esystem_of_exp e) inputs in
    match inputs with
    | [] ->
      step_invariant_init e;
      (| t.init, [], XB.BSs0 e, () |)
    | i :: inputs' ->
      let (| s, results, hBSs, prf |) = system_invariant_many inputs' e in
      let (| r, hBS |) = XC.lemma_bigstep_total (i :: inputs') e in
      step_invariant_step inputs' i e r hBS s;
      assert (E.esystem_steps (EX.esystem_of_exp e)       inputs'  == (s ,      results));
      assert (E.esystem_steps (EX.esystem_of_exp e)       inputs   == (s', r :: results));
      let hBSs': XB.bigsteps (i :: inputs') e (r :: results) = XB.BSsS _ e _ _ _ hBSs hBS in
      (| s', r :: results, hBSs', () |)


(* Section 5, Theorem 5, execution-equivalence *)
let esystem_execution_equivalence
    (#t: table) (#c: context t) (#a: t.ty)
    (inputs: list (row c))
    (e: exp t c a { XC.causal e })
    : Lemma (ensures
        snd (E.esystem_steps (EX.esystem_of_exp e) inputs) == XC.lemma_bigsteps_total_vs inputs e
      ) =
  let (| _vs, hBSs |) = XC.lemma_bigsteps_total inputs e in
  let (| s, results', hBSs', prf |) = system_invariant_many inputs e in
  XB.bigsteps_proof_equivalence hBSs hBSs';
  ()
