(* Proofs related to abstract transition systems (Section 4) *)
module Pipit.System.Exp.Properties

open Pipit.Prim.Table
open Pipit.Exp.Base

module Table = Pipit.Prim.Table

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties

module SB = Pipit.System.Base
module SX = Pipit.System.Exp

module X  = Pipit.Exp
module XB = Pipit.Exp.Bigstep
module XC = Pipit.Exp.Causality
module XBind = Pipit.Exp.Binding

module List = FStar.List.Tot

module T    = FStar.Tactics

#set-options "--split_queries always"

(* --------------------------------------------------------------------------
   type_join projection rewrites.

   The fused loop's oracle/state types have a NON-literal second component
   (`type_join (state_of_exp f) (state_of_exp g)`), so `type_join_fst`/
   `type_join_snd` of a `type_join_tup` do NOT reduce by computation (the match
   on the component option types is stuck).  These two rewrites discharge them
   by a small case-analysis on the component types, and fire automatically
   (SMTPat), so every projection obligation of the abstract systems (XMufby,
   but also XMu/XLet/XContract/XApp) becomes a tiny deterministic query instead
   of a hand-written `assert`.  This is the main de-flaking lever for the
   fused-loop soundness proofs. *)
let lemma_type_join_fst_tup (#t1 #t2: option Type)
  (v1: SB.option_type_sem t1) (v2: SB.option_type_sem t2)
  : Lemma (ensures SB.type_join_fst #t1 #t2 (SB.type_join_tup #t1 #t2 v1 v2) == v1)
    [SMTPat (SB.type_join_fst #t1 #t2 (SB.type_join_tup #t1 #t2 v1 v2))] =
  match t1, t2 with
  | Some _, Some _ -> ()
  | None, _ -> ()
  | _, None -> ()

let lemma_type_join_snd_tup (#t1 #t2: option Type)
  (v1: SB.option_type_sem t1) (v2: SB.option_type_sem t2)
  : Lemma (ensures SB.type_join_snd #t1 #t2 (SB.type_join_tup #t1 #t2 v1 v2) == v2)
    [SMTPat (SB.type_join_snd #t1 #t2 (SB.type_join_tup #t1 #t2 v1 v2))] =
  match t1, t2 with
  | Some _, Some _ -> ()
  | None, _ -> ()
  | _, None -> ()

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

  | XMufby acc seed f g ->
    // system_mufby state = (register acc, (f-state, g-state)).  The register
    // holds the accumulator fed next; f runs on the *operational* accumulator
    // stream `accsys = seed fby g(mres)` (exactly the register value), and g
    // runs on the output stream `mres = mufby_desugar seed f g`.
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem acc)) (SB.type_join (SX.state_of_exp f) (SX.state_of_exp g))) = s in
    let reg_acc = SB.type_join_fst s in
    let inner = SB.type_join_snd s in
    let sf = SB.type_join_fst inner in
    let sg = SB.type_join_snd inner in
    let mres = XBind.mufby_desugar seed f g in
    let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
    XC.lemma_causal_XMufby seed f g;
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows) f sf /\
    system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows) g sg /\
    (match rows with
     | [] -> reg_acc == seed
     | _ :: _ -> XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc)

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
    let f0: funty_sem t.ty_sem (FTVal a) -> unit -> funty_sem t.ty_sem (FTVal a) = SX.system_of_exp_apps_const in
    step_apps_invariant_init e1 f0;
    assert_norm ((SX.system_of_exp (XApps e1)).init == (SX.system_of_exp_apps e1 f0).init);
    ()

  | XFby v1 e2 ->
    invariant_init e2

  | XMu e1 ->
    invariant_init e1;
    ()

  | XMufby acc seed f g ->
    XC.lemma_causal_XMufby seed f g;
    invariant_init f;
    invariant_init g;
    // Reduce the fused-loop initial state to its `type_join_tup` structure so
    // SMT can discharge the register/sub-state projections in the invariant.
    assert ((SX.system_of_exp (XMufby acc seed f g)).init ==
      SB.type_join_tup #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) seed
        (SB.type_join_tup #(SX.state_of_exp f) #(SX.state_of_exp g) (SX.system_of_exp f).init (SX.system_of_exp g).init))
      by (T.norm [delta_only [`%SX.system_of_exp; `%SB.system_mufby]; zeta; primops; iota; nbe]; T.trefl ());
    let inner0 : SB.option_type_sem (SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) =
      SB.type_join_tup #(SX.state_of_exp f) #(SX.state_of_exp g) (SX.system_of_exp f).init (SX.system_of_exp g).init in
    let s0 : SB.option_type_sem (SX.state_of_exp (XMufby acc seed f g)) =
      SB.type_join_tup #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) seed inner0 in
    assert (SB.type_join_fst #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) s0 == seed);
    assert (SB.type_join_snd #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g)) s0 == inner0);
    assert (SB.type_join_fst #(SX.state_of_exp f) #(SX.state_of_exp g) inner0 == (SX.system_of_exp f).init);
    assert (SB.type_join_snd #(SX.state_of_exp f) #(SX.state_of_exp g) inner0 == (SX.system_of_exp g).init);
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

  | XMufby acc seed f g ->
    // Oracle for the fused loop: the loop is causal-by-construction, so there
    // is NO res-knot oracle -- only f's and g's own oracles, drawn from the
    // recursion on the operational accumulator stream `accsys` and the output
    // stream `mres` respectively.
    let mres = XBind.mufby_desugar seed f g in
    let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
    XC.lemma_causal_XMufby seed f g;
    let avs = XC.lemma_bigsteps_total_vs rows accsys in
    let rows_f = CR.extend1 avs rows in
    let orf = step_oracle rows_f f in
    let mvs = XC.lemma_bigsteps_total_vs rows mres in
    let rows_g = CR.extend1 mvs rows in
    let og = step_oracle rows_g g in
    SB.type_join_tup #(SX.oracle_of_exp f) #(SX.oracle_of_exp g) orf og

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

(* Congruence for the invariant under state equality.  Used to transfer the
   invariant, established on an explicitly-reconstructed state `s'`, to the
   operational step output `stp.s` (== s') without re-unfolding the invariant on
   the opaque step result. *)
let lemma_system_of_exp_invariant_cong
    (#t: table) (#c: context t) (#a: t.ty)
    (rows: list (row c))
    (e: exp t c a { XC.causal e })
    (s1 s2: SB.option_type_sem (SX.state_of_exp e))
    : Lemma (requires s1 == s2 /\ system_of_exp_invariant rows e s1)
        (ensures system_of_exp_invariant rows e s2) = ()

#push-options "--fuel 4 --ifuel 2 --z3rlimit 300"

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
    assert_norm (SX.state_of_exp (XApps e1) == SX.state_of_exp_apps e1);
    let s: SB.option_type_sem (SX.state_of_exp_apps e1) = s in
    let f0: funty_sem t.ty_sem (FTVal a) -> unit -> funty_sem t.ty_sem (FTVal a) = SX.system_of_exp_apps_const in
    invariant_step_apps rows row1 e1 f0 () s

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

  | XMufby acc seed f g ->
    // Oracle-free single-evaluation bisimulation for the fused loop.
    //
    // system_mufby.step reads reg_acc = type_join_fst s, runs f ONCE on
    // (reg_acc, row1) with f's own oracle to compute the output res = stpf.v,
    // then g ONCE on (res, row1) with g's oracle to get the next accumulator
    // acc'; it OUTPUTS res and stores (acc', (sf', sg')).  The f-side tracks
    // the *operational* accumulator stream accsys = seed fby g(mres) (the
    // register value), the g-side tracks the output stream mres.  There is no
    // res-oracle: the output equals the true desugar output because f applied
    // to the accumulator stream IS the desugar output (single evaluation).
    let mres = XBind.mufby_desugar seed f g in
    let accsys : exp t c acc = XFby seed (XBind.subst1 g mres) in
    XC.lemma_causal_XMufby seed f g;
    let s: SB.option_type_sem (SB.type_join (Some (t.ty_sem acc)) (SB.type_join (SX.state_of_exp f) (SX.state_of_exp g))) = s in
    let reg_acc = SB.type_join_fst s in
    let inner = SB.type_join_snd s in
    let sf = SB.type_join_fst inner in
    let sg = SB.type_join_snd inner in
    // Expose the current-state invariant conjuncts while the refinement is fresh.
    assert (system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows) f sf);
    assert (system_of_exp_invariant (CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows) g sg);
    assert (match rows with
            | [] -> reg_acc == seed
            | _ :: _ -> XB.bigstep_prop rows (XBind.subst1 g mres) reg_acc);

    // (A) The output value is the desugar's output.
    let (| v, hBS |) = XC.lemma_bigstep_total (row1 :: rows) (XMufby acc seed f g) in
    let hBS_mres : XB.bigstep (row1 :: rows) mres v =
      (match hBS with | XB.BSMufby _ _ _ _ _ h -> h) in

    // (B) The accumulator value stream's head equals the register value.
    XC.lemma_bigstep_mufby_accsys_head seed f g rows row1 reg_acc;

    // (C) Bridge both extended histories to CR.cons form (so step_oracle's f/g
    //     oracle components and the recursion histories line up).
    let rows_f = CR.extend1 (XC.lemma_bigsteps_total_vs rows accsys) rows in
    let rows_g = CR.extend1 (XC.lemma_bigsteps_total_vs rows mres) rows in
    XC.lemma_extend1_value_stream_cons rows row1 accsys;
    XC.lemma_extend1_value_stream_cons rows row1 mres;
    // mres head == v (the loop output).
    introduce exists (h: XB.bigstep (row1 :: rows) mres v). True with hBS_mres and ();
    XB.bigstep_deterministic_squash (row1 :: rows) mres v (XC.lemma_bigstep_total_v (row1 :: rows) mres);
    assert (CR.extend1 (XC.lemma_bigsteps_total_vs (row1 :: rows) accsys) (row1 :: rows) == CR.cons reg_acc row1 :: rows_f);
    assert (CR.extend1 (XC.lemma_bigsteps_total_vs (row1 :: rows) mres) (row1 :: rows) == CR.cons v row1 :: rows_g);

    // (D) THE OUTPUT FIXPOINT: f applied to the accumulator stream equals the
    //     desugar output v (single evaluation).  From bigstep mres v extract
    //     bigstep (subst1 f accsys) v (desugar_output), then eliminate the
    //     substitution to get bigstep (extend1 avs (row1::rows)) f v; that
    //     history is exactly CR.cons reg_acc row1 :: rows_f, so f's canonical
    //     value there is v.
    let (| avs, hBSaccsys |) = XC.lemma_bigsteps_total (row1 :: rows) accsys in
    let hBS_subst : XB.bigstep (row1 :: rows) (XBind.subst1 f accsys) v =
      XC.lemma_bigstep_mufby_desugar_output (row1 :: rows) seed f g v hBS_mres in
    let hBS_f : XB.bigstep (CP.row_zip2_lift1_dropped 0 (row1 :: rows) avs) f v =
      XC.lemma_bigstep_substitute_elim 0 (row1 :: rows) accsys avs f v hBSaccsys hBS_subst in
    // row_zip2_lift1_dropped 0 rows avs == CR.extend1 avs rows (SMTPat), and that
    // extended history is CR.cons reg_acc row1 :: rows_f; so f's canonical value
    // there is v, hence stpf.v == v below.
    introduce exists (h: XB.bigstep (CP.row_zip2_lift1_dropped 0 (row1 :: rows) avs) f v). True with hBS_f and ();
    assert (CR.extend1 avs (row1 :: rows) == CR.cons reg_acc row1 :: rows_f);
    XB.bigstep_deterministic_squash (CR.cons reg_acc row1 :: rows_f) f v
      (XC.lemma_bigstep_total_v (CR.cons reg_acc row1 :: rows_f) f);

    // (C') New accumulator register fact acc' = g's output over the mres history.
    let (| mvs, hBSmres' |) = XC.lemma_bigsteps_total (row1 :: rows) mres in
    let XB.BSsS _ _ mvs_tl _ mv_hd hBSmres_tl hBSmres_head = hBSmres' in
    XB.bigstep_deterministic hBS_mres hBSmres_head;   // mv_hd == v (the mres head is the output)
    assert (CR.extend1 mvs (row1 :: rows) == CR.cons v row1 :: rows_g);
    let (| v_g, hBS_g0 |) = XC.lemma_bigstep_total (CR.extend1 mvs (row1 :: rows)) g in
    let hBSreg : XB.bigstep (row1 :: rows) (XBind.subst1 g mres) v_g =
      XC.lemma_bigstep_substitute_intros 0 (row1 :: rows) mres mvs g v_g hBSmres' hBS_g0 in

    // (E) Recurse on f and g (with the histories/oracles step_oracle uses).
    invariant_step rows_f (CR.cons reg_acc row1) f sf;
    invariant_step rows_g (CR.cons v      row1) g sg;

    // (F) Reconstruct the operational sub-steps.  step_oracle's f/g components
    //     are exactly these (via the history bridge + reg_acc alignment).  The
    //     recursion gives stpf.v == canonical f value == v, and stpg.v == v_g.
    let stpf = (SX.system_of_exp f).step (CR.cons reg_acc row1) (step_oracle (CR.cons reg_acc row1 :: rows_f) f) sf in
    let stpg = (SX.system_of_exp g).step (CR.cons v      row1) (step_oracle (CR.cons v      row1 :: rows_g) g) sg in
    assert (stpf.v == v);
    assert (stpg.v == v_g);

    let s' : SB.option_type_sem (SX.state_of_exp (XMufby acc seed f g)) =
      SB.type_join_tup #(Some (t.ty_sem acc)) #(SB.type_join (SX.state_of_exp f) (SX.state_of_exp g))
        stpg.v (SB.type_join_tup #(SX.state_of_exp f) #(SX.state_of_exp g) stpf.s stpg.s) in
    // register bigstep for the new accumulator acc' == v_g == stpg.v
    introduce exists (h: XB.bigstep (row1 :: rows) (XBind.subst1 g mres) stpg.v). True
      with hBSreg and ();
    // type_join projections of s' reduce via the SMTPat rewrites above.
    assert (system_of_exp_invariant (row1 :: rows) (XMufby acc seed f g) s');

    // (G) Output correspondence + invariant transfer to the opaque step output.
    let stp = (SX.system_of_exp e).step row1 (step_oracle (row1 :: rows) e) s in
    // Align step_oracle's f/g oracle components with the recursion oracles.
    let o_all = step_oracle (row1 :: rows) (XMufby acc seed f g) in
    assert (SB.type_join_fst #(SX.oracle_of_exp f) #(SX.oracle_of_exp g) o_all
              == step_oracle (CR.cons reg_acc row1 :: rows_f) f);
    assert (SB.type_join_snd #(SX.oracle_of_exp f) #(SX.oracle_of_exp g) o_all
              == step_oracle (CR.cons v row1 :: rows_g) g);
    assert (stp.v == v);
    assert (stp.s == s');
    lemma_system_of_exp_invariant_cong (row1 :: rows) e s' stp.s;
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

#pop-options


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
