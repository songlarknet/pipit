(* Bigstep semantics for expressions.
   This is a bit different from the standard "reactive step" operational
   semantics. The reactive step semantics operate under a single environment and
   allow an expression e to step to a new expression e', producing a value. In
   contrast, the bigstep relation here takes a stream of environments, and
   fully evaluates an expression to a value.
   The bigstep semantics feels a lot more functional (applicative), while the
   reactive step semantics better matches the actual streaming execution mode.

   We prove that the semantics is deterministic here. The statement of
   "progress" says that for every list of inputs there exists an output; this
   property only holds for causal programs, so we prove it in the
   `Pipit.Exp.Causality` module.
*)
module Pipit.Exp.Bigstep

open Pipit.Prim.Table

open Pipit.Exp.Base
open Pipit.Exp.Binding

module C  = Pipit.Context.Base
module CR = Pipit.Context.Row
module CP = Pipit.Context.Properties
module PM = Pipit.Prop.Metadata

module List = FStar.List

(* bigstep_base streams e v

 Bigstep semantics: in streaming history `streams`, which is a sequence of
 environments, the expression `e` evaluates to value `v`.
 The stream history `streams` is in most-recent-first order.
 *)
[@@no_auto_projectors]
noeq
type bigstep_base (#t: table u#i u#j) (#c: context t): (#a: t.ty) -> list (row c) -> exp_base t c a -> t.ty_sem a -> Type =
 (* Values `v` always evaluate to the value *)
 | BSVal:
          #valty: t.ty ->
          streams: list (row c) ->
          v: t.ty_sem valty ->
          bigstep_base streams (XVal v) v

 (* Variables `x` are looked up in the most recent row in the stream history *)
 | BSVar: latest: row c ->
          prefix: list (row c) ->
          x: C.index_lookup c ->
          bigstep_base (latest :: prefix) (XBVar x) (CR.index (context_sem c) latest x)

 (* Free variables `XVar` have no evaluation rule - they aren't in the local `streams` environment *)

(* bigstep streams e v *)
[@@no_auto_projectors]
noeq
type bigstep (#t: table u#i u#j) (#c: context t): (#a: t.ty) -> list (row c) -> exp t c a -> t.ty_sem a -> Type u#(max i j) =
 (* Base expressions *)
 | BSBase:
          #valty: t.ty ->
          streams: list (row c)    ->
          e: exp_base t c valty    ->
          v: t.ty_sem valty        ->
          bigstep_base streams e v ->
          bigstep streams (XBase e) v

 (* Applications *)
 | BSApps:
          #valty: t.ty ->
          streams: list (row c)    ->
          e: exp_apps t c
                  (FTVal valty)    ->
          v: t.ty_sem valty        ->
          bigstep_apps streams e v ->
          bigstep streams (XApps e) v

 (* At the very first step, `v fby e` evaluates to `v`. *)
 | BSFby1: #a: t.ty                ->
           start: list (row c) { List.Tot.length start <= 1 }
                                   ->
           v0: t.ty_sem a          ->
           e: exp t c a            ->
           bigstep start (XFby v0 e) v0
 (* To compute `pre e` we evaluate `e` without the most recent element. *)
 | BSFbyS: #a: t.ty                 ->
           latest: row c            ->
           prefix: list (row c) { List.Tot.length prefix >= 1 }
                                    ->
           v0: t.ty_sem a           ->
           v': t.ty_sem a           ->
           e: exp t c a             ->
           bigstep            prefix           e  v' ->
           bigstep (latest :: prefix) (XFby v0 e) v'

 (* Reduction for recursive expressions proceeds by unfolding the recursion one step.
    If all recursive references are guarded by `pre` then the `pre` step will look
    at a shorter stream history prefix, and will eventually terminate. *)
 | BSMu: #valty: t.ty                         ->
         streams: list (row c)                ->
         e: exp t (C.close1 c valty) valty    ->
         v: t.ty_sem valty                    ->
         bigstep streams (subst1 e (XMu e)) v ->
         bigstep streams (XMu e) v

 (* Let expressions are performed by substituting into the expression.
    We could also evaluate the definition e1 to a stream of values, and add each
    of these to the stream contexts - but this is a bit easier, and later we can
    prove that they're equivalent. *)
 | BSLet:
          #a: t.ty -> #b: t.ty                ->
          streams: list (row c)               ->
          e1: exp t c b                       ->
          e2: exp t (C.close1 c b) a          ->
          v:  t.ty_sem a                      ->
          bigstep streams (subst1 e2 e1) v    ->
          bigstep streams (XLet b e1 e2) v

 (* To evaluate a contract, we just use the implementation. We want to be able
    to show that the evaluation is a refinement of the rely/guarantee. *)
 | BSContract:
          #valty: t.ty                        ->
          streams: list (row c)               ->
          status: PM.contract_status          ->
          rely: exp t c            t.propty   ->
          guar: exp t (valty :: c) t.propty   ->
          impl: exp t c            valty      ->
          v: t.ty_sem valty                   ->
          bigstep streams impl v                ->
          bigstep streams (XContract status rely guar impl) v

 (* We evaluate properties, but we don't actually check that the properties are
    true in this semantics. We want to be able to prove that the transition
    system preserves semantics, whether or not the properties are true. *)
 | BSCheck:
          streams: list (row c)                   ->
          status:  PM.prop_status                 ->
          eprop:   exp t c             t.propty   ->
          v:       t.ty_sem t.propty              ->
          bigstep streams                eprop  v ->
          bigstep streams (XCheck status eprop) ()

and bigstep_apps (#t: table) (#c: context t): (#a: funty t.ty) -> list (row c) -> exp_apps t c a -> funty_sem t.ty_sem a -> Type =

 (* Primitives `p` are looked up in the primitive table semantics *)
 | BSPrim:
          streams: list (row c) ->
          p: t.prim             ->
          bigstep_apps streams (XPrim p) (t.prim_sem p)

 (* Element-wise application *)
 | BSApp: streams: list (row c)       ->
          #a: t.ty -> #b: funty t.ty  ->
          f: exp_apps t c (FTFun a b) ->
          e: exp t c  a               ->
          f_v: funty_sem t.ty_sem (FTFun a b) ->
          e_v: t.ty_sem a                     ->
          bigstep_apps streams f f_v          ->
          bigstep      streams e e_v          ->
          bigstep_apps streams (XApp f e) (f_v e_v)

(* Under streaming history `streams`, evaluate expression `e` at each step to
   produce stream of values `vs` *)
[@@no_auto_projectors]
noeq
type bigsteps (#t: table u#i u#j) (#c: context t) (#a: t.ty): list (row c) -> exp t c a -> list (t.ty_sem a) -> Type =
 | BSs0:
    e: exp t c a                        ->
    bigsteps [] e []
 | BSsS:
    rows: list (row c)                  ->
    e: exp t c a                        ->
    vs: list (t.ty_sem a)               ->
    row: row c                          ->
    v: t.ty_sem a                       ->
    bigsteps        rows  e      vs     ->
    bigstep  (row :: rows) e  v         ->
    bigsteps (row :: rows) e (v :: vs)


(* Many-bigstep is a Type, but a prop is useful for extending the context.
  Extending the context also requires the lengths to match *)
let bigsteps_prop (#t: table u#i u#j) (#c: context t) (#a: t.ty)
  (rows: list (row c))
  (e: exp t c a)
  (vs: list (t.ty_sem a)) =
  List.length rows == List.length vs /\
  squash (bigsteps rows e vs)

let rec bigstep_always (#t: table u#i u#j) (#c: context t)
  (rows: list (row c))
  (e: exp t c t.propty): Tot prop (decreases rows) =
  match rows with
  | [] -> True
  | row1 :: rows' ->
    // XXX: squash: bigstep_always shows up in refinements, so it's useful to have it as prop.
    // If this causes issues, try lifting to Type; requires changing Pipit.Exp.Checked.Base too
    squash (bigstep rows e true) /\
    bigstep_always rows' e

let bigstep_always_cons (#t: table u#i u#j) (#c: context t)
  (rows: list (row c))
  (row1: row c)
  (e: exp t c t.propty): Lemma
    (bigstep_always (row1 :: rows) e <==> (squash (bigstep (row1 :: rows) e true) /\ bigstep_always rows e))
    [SMTPat (bigstep_always (row1 :: rows) e)]
     =
  assert (bigstep_always (row1 :: rows) e <==> (squash (bigstep (row1 :: rows) e true) /\ bigstep_always rows e))
    by (FStar.Tactics.norm [delta_only [`%bigstep_always]; zeta; iota]);
  ()


(* Properties *)
let bigstep_base_proof_equivalence
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (#streams: list (row c))
  (#e: exp_base t c a)
  (#v1 #v2: t.ty_sem a)
  (hBS1: bigstep_base streams e v1) (hBS2: bigstep_base streams e v2):
    Lemma (ensures hBS1 === hBS2) (decreases hBS1) =
  match hBS1 with
  | BSVal _ _  -> ()
  | BSVar _ _ _ -> ()


let rec bigstep_proof_equivalence
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (#streams: list (row c))
  (#e: exp t c a)
  (#v1 #v2: t.ty_sem a)
  (hBS1: bigstep streams e v1) (hBS2: bigstep streams e v2):
    Lemma (ensures hBS1 === hBS2) (decreases hBS1) =
  match hBS1 with
  | BSBase _ _ _ bs11 ->
    let BSBase _ _ _ bs21 = hBS2 in
    bigstep_base_proof_equivalence bs11 bs21

  | BSApps _ _ _ bs11 ->
    let BSApps _ _ _ bs21 = hBS2 in
    bigstep_apps_proof_equivalence bs11 bs21

  | BSFby1 _ _ _ ->
    ()
  | BSFbyS _ _ _ _ _ bs1 ->
    let BSFbyS _ _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSMu _ _ _ bs1 ->
    let BSMu _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSLet _ _ _ _ bs1 ->
    let BSLet _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSContract _ _ _ _ _ _ bsi1 ->
    let BSContract _ _ _ _ _ _ bsi2 = hBS2 in
    bigstep_proof_equivalence bsi1 bsi2

  | BSCheck _ _ _ _ bs1 ->
    let BSCheck _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

and bigstep_apps_proof_equivalence
  (#t: table)
  (#c: context t)
  (#a: funty t.ty)
  (#streams: list (row c))
  (#e: exp_apps t c a)
  (#v1 #v2: funty_sem t.ty_sem a)
  (hBS1: bigstep_apps streams e v1) (hBS2: bigstep_apps streams e v2):
    Lemma (ensures hBS1 === hBS2) (decreases hBS1) =
  match hBS1 with
  | BSPrim _ _ ->
    ()
  | BSApp _ _ _ _ _ bs11 bs12 ->
    let BSApp _ _ _ _ _ bs21 bs22 = hBS2 in
    bigstep_apps_proof_equivalence bs11 bs21;
    bigstep_proof_equivalence bs12 bs22

let rec bigsteps_proof_equivalence
  (#t: table)
  (#c: context t)
  (#a: t.ty)
  (#streams: list (row c))
  (#e: exp t c a)
  (#vs1 #vs2: list (t.ty_sem a))
  (hBS1: bigsteps streams e vs1) (hBS2: bigsteps streams e vs2):
    Lemma (ensures hBS1 === hBS2) (decreases hBS1) =
  match hBS1 with
  | BSs0 _ ->
    ()
  | BSsS _ _ _ _ _ bs11 bs12 ->
    let BSsS _ _ _ _ _ bs21 bs22 = hBS2 in
    bigsteps_proof_equivalence bs11 bs21;
    bigstep_proof_equivalence bs12 bs22



let bigstep_deterministic
  (#t: table)
  (#c: context t)
  (#streams: list (row c))
  (#a: t.ty)
  (#e: exp t c a)
  (#v1 #v2: t.ty_sem a)
  (hBS1: bigstep streams e v1) (hBS2: bigstep streams e v2):
    Lemma (ensures (v1 == v2)) (decreases hBS1) =
  bigstep_proof_equivalence hBS1 hBS2


let bigstep_deterministic_squash
  (#t: table)
  (#c: context t)
  (streams: list (row c))
  (#a: t.ty)
  (e: exp t c a)
  (v1 v2: t.ty_sem a):
    Lemma
      (requires (bigstep streams e v1 /\ bigstep streams e v2))
      (ensures (v1 == v2)) =
  FStar.Squash.bind_squash #(bigstep streams e v1) ()
    (fun (a: bigstep streams e v1) ->
  FStar.Squash.bind_squash #(bigstep streams e v2) #(v1 == v2) ()
    (fun (b: bigstep streams e v2) ->
      bigstep_deterministic a b))
