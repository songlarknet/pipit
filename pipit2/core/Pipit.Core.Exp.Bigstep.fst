module Pipit.Core.Exp.Bigstep

module PR  = Pipit.Core.Exp.Prim
module PP  = Pipit.Core.Exp.Pure
module PES = Pipit.Core.Exp.Source
module PM  = Pipit.Base.Prop.Metadata
module L   = FStar.List.Tot

type tuple = list PR.value
type row = list tuple

[@@no_auto_projectors]
noeq
type bigstep (env: PES.sigenv) (venv: PP.val_context): list row -> PES.term -> tuple -> Type =
  | BSPure:
      streams: list row ->
      p: PP.pterm ->
      v: PR.value ->
      squash (PP.pterm_sem venv p == Some v) ->
      bigstep env venv streams (PES.XPure p) [v]

  | BSVar:
      latest: row ->
      prefix: list row ->
      i: nat ->
      squash (i < L.length latest) ->
      bigstep env venv (latest :: prefix) (PES.XBVar i) (L.index latest i)

  | BSFby1:
      start: list row { L.length start <= 1 } ->
      v0s: list PP.pterm ->
      es: list PES.term ->
      vs: list PR.value ->
      squash (PP.sem_args venv v0s == Some vs) ->
      bigstep env venv start (PES.XFby v0s es) vs

  | BSFbyS:
      latest: row ->
      prefix: list row { L.length prefix >= 1 } ->
      v0s: list PP.pterm ->
      es: list PES.term ->
      vs: list PR.value ->
      bigstep_widths env venv prefix es vs ->
      bigstep env venv (latest :: prefix) (PES.XFby v0s es) vs

  | BSPrim:
      streams: list row ->
      p: PR.prim ->
      arg: PES.term ->
      vs: list PR.value ->
      r: PR.value ->
      bigstep env venv streams arg vs ->
      squash (PR.prim_sem p vs == Some r) ->
      bigstep env venv streams (PES.XPrim p arg) [r]

  | BSTuple:
      streams: list row ->
      es: list PES.term ->
      ws: list PR.value ->
      bigstep_widths env venv streams es ws ->
      bigstep env venv streams (PES.XTuple es) ws

  | BSNode:
      streams: list row ->
      nm: string ->
      args: list PES.term ->
      nd: PES.node ->
      body: PES.term ->
      v: list PR.value ->
      squash (L.assoc nm env.nodes == Some nd /\ nd.body == Some body) ->
      bigstep env venv streams (PES.inst_node nd.params args body) v ->
      bigstep env venv streams (PES.XNode nm args) v

  | BSProj:
      streams: list row ->
      j: nat ->
      e: PES.term ->
      vs: list PR.value ->
      squash (j < L.length vs) ->
      bigstep env venv streams e vs ->
      bigstep env venv streams (PES.XProj j e) [L.index vs j]

  | BSMu:
      streams: list row ->
      tys: list PR.typ ->
      body: PES.term ->
      v: list PR.value ->
      bigstep env venv streams (PES.subst_tuple (PES.XMu tys body) body) v ->
      bigstep env venv streams (PES.XMu tys body) v

  | BSLet:
      streams: list row ->
      tys: list PR.typ ->
      rhs: PES.term ->
      body: PES.term ->
      v: list PR.value ->
      bigstep env venv streams (PES.subst_tuple rhs body) v ->
      bigstep env venv streams (PES.XLet tys rhs body) v

  | BSContract:
      streams: list row ->
      s: PM.contract_status ->
      rely: PES.term ->
      guar: PES.term ->
      impl: PES.term ->
      v: list PR.value ->
      bigstep env venv streams impl v ->
      bigstep env venv streams (PES.XContract s rely guar impl) v

  | BSCheck:
      streams: list row ->
      s: PM.prop_status ->
      e: PES.term ->
      vp: PR.value ->
      bigstep env venv streams e [vp] ->
      bigstep env venv streams (PES.XCheck s e) []

and bigstep_widths (env: PES.sigenv) (venv: PP.val_context): list row -> list PES.term -> list PR.value -> Type =
  | BSW0:
      streams: list row ->
      bigstep_widths env venv streams [] []
  | BSWS:
      streams: list row ->
      e: PES.term ->
      es: list PES.term ->
      w: list PR.value ->
      ws: list PR.value ->
      bigstep env venv streams e w ->
      bigstep_widths env venv streams es ws ->
      bigstep_widths env venv streams (e :: es) (L.append w ws)

[@@no_auto_projectors]
noeq
type bigsteps (env: PES.sigenv) (venv: PP.val_context): list row -> PES.term -> list (list PR.value) -> Type =
  | BSs0:
      e: PES.term ->
      bigsteps env venv [] e []
  | BSsS:
      rows: list row ->
      e: PES.term ->
      vs: list (list PR.value) ->
      r: row ->
      v: list PR.value ->
      bigsteps env venv rows e vs ->
      bigstep env venv (r :: rows) e v ->
      bigsteps env venv (r :: rows) e (v :: vs)

let bigstep_prop (env: PES.sigenv) (venv: PP.val_context) (streams: list row) (e: PES.term) (v: list PR.value): prop =
  exists (h: bigstep env venv streams e v). True

let rec bigstep_det
  (#env: PES.sigenv) (#venv: PP.val_context) (#streams: list row) (#e: PES.term) (#v1 #v2: list PR.value)
  (h1: bigstep env venv streams e v1) (h2: bigstep env venv streams e v2)
  : Lemma (ensures v1 == v2) (decreases h1) =
  match h1 with
  | BSPure _ _ _ _ ->
    let BSPure _ _ _ _ = h2 in ()
  | BSVar _ _ _ _ ->
    let BSVar _ _ _ _ = h2 in ()
  | BSFby1 _ _ _ _ _ ->
    (match h2 with
     | BSFby1 _ _ _ _ _ -> ()
     | BSFbyS _ _ _ _ _ _ -> ())
  | BSFbyS _ _ _ _ _ hb1 ->
    (match h2 with
     | BSFby1 _ _ _ _ _ -> ()
     | BSFbyS _ _ _ _ _ hb2 -> bigstep_widths_det hb1 hb2)
  | BSPrim _ _ _ _ _ hs1 _ ->
    let BSPrim _ _ _ _ _ hs2 _ = h2 in
    bigstep_det hs1 hs2
  | BSTuple _ _ _ hw1 ->
    let BSTuple _ _ _ hw2 = h2 in
    bigstep_widths_det hw1 hw2
  | BSNode _ nm _ nd1 body1 _ _ hb1 ->
    let BSNode _ _ _ nd2 body2 _ _ hb2 = h2 in
    assert (nd1 == nd2);
    assert (body1 == body2);
    bigstep_det hb1 hb2
  | BSProj _ _ _ _ _ hb1 ->
    let BSProj _ _ _ _ _ hb2 = h2 in
    bigstep_det hb1 hb2
  | BSMu _ _ _ _ hb1 ->
    let BSMu _ _ _ _ hb2 = h2 in
    bigstep_det hb1 hb2
  | BSLet _ _ _ _ _ hb1 ->
    let BSLet _ _ _ _ _ hb2 = h2 in
    bigstep_det hb1 hb2
  | BSContract _ _ _ _ _ _ hb1 ->
    let BSContract _ _ _ _ _ _ hb2 = h2 in
    bigstep_det hb1 hb2
  | BSCheck _ _ _ _ _ ->
    let BSCheck _ _ _ _ _ = h2 in ()

and bigstep_widths_det
  (#env: PES.sigenv) (#venv: PP.val_context) (#streams: list row) (#es: list PES.term) (#ws1 #ws2: list PR.value)
  (h1: bigstep_widths env venv streams es ws1) (h2: bigstep_widths env venv streams es ws2)
  : Lemma (ensures ws1 == ws2) (decreases h1) =
  match h1 with
  | BSW0 _ ->
    let BSW0 _ = h2 in ()
  | BSWS _ _ _ _ _ hb1 ht1 ->
    let BSWS _ _ _ _ _ hb2 ht2 = h2 in
    bigstep_det hb1 hb2;
    bigstep_widths_det ht1 ht2
