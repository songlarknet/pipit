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

(* bigstep streams e v

 Bigstep semantics: in streaming history `streams`, which is a sequence of
 environments, the expression `e` evaluates to value `v`.
 The stream history `streams` is in most-recent-first order.
 *)
noeq
type bigstep (#t: table) (#c: context t): (#a: Type0) -> list (row c) -> exp t c a -> a -> Type =
 (* Values `v` always evaluate to the value *)
 | BSVal:
          #valty: t.ty ->
          streams: list (row c) ->
          v: t.ty_sem valty ->
          bigstep streams (XVal v) v

 (* Variables `x` are looked up in the most recent row in the stream history *)
 | BSVar: latest: row c ->
          prefix: list (row c) ->
          x: C.index_lookup c ->
          bigstep (latest :: prefix) (XBVar x) (CR.index (context_sem c) latest x)

 (* Free variables `XVar` have no evaluation rule - they aren't on the local `streams` environment *)

 (* Primitives `p` are looked up in the primitive table semantics *)
 | BSPrim:
          streams: list (row c) ->
          p: t.prim ->
          bigstep streams (XPrim p) (t.prim_sem p)

 (* Element-wise application *)
 | BSApp: streams: list (row c) ->
          f: exp t c ('a -> 'b)        ->
          e: exp t c  'a             ->
          f_v: ('a -> 'b)            ->
          e_v:  'a                 ->
          bigstep streams f f_v   ->
          bigstep streams e e_v   ->
          bigstep streams (XApp f e) (f_v e_v)

 (* To compute `pre e` we evaluate `e` without the most recent element. *)
 | BSFby1: #a: eqtype ->
           start: list (row c) { List.Tot.length start <= 1 }
                                    ->
           v0: a                    ->
           e: exp t c a               ->
           bigstep start (XFby v0 e) v0
 (* To compute `pre e` we evaluate `e` without the most recent element. *)
 | BSFbyS: #a: eqtype ->
           latest: row c          ->
           prefix: list (row c) { List.Tot.length prefix >= 1 }
                                    ->
           v0: a                    ->
           v': a                    ->
           e: exp t c a               ->
           bigstep           prefix           e  v' ->
           bigstep (latest :: prefix) (XFby v0 e) v'

 (* First step of (p -> q) is p *)
 | BSThen1: #a: eqtype ->
            start: list (row c) { List.Tot.length start <= 1 }
                                    ->
            e1: exp t c a             ->
            e2: exp t c a             ->
            v: a                    ->
            bigstep start        e1     v ->
            bigstep start (XThen e1 e2) v
 (* Subsequent steps of (p -> q) are q *)
 | BSThenS: #a: eqtype ->
            streams: list (row c) { List.Tot.length streams > 1 }
                                    ->
            e1: exp t c a             ->
            e2: exp t c a             ->
            v: a                    ->
            bigstep streams           e2  v ->
            bigstep streams (XThen e1 e2) v

 (* Reduction for recursive expressions proceeds by unfolding the recursion one step.
    If all recursive references are guarded by `pre` then the `pre` step will look
    at a shorter stream history prefix, and should eventually terminate. *)
 | BSMu: #valty: t.ty ->
         streams: list (row c)    ->
         e: val_exp t (C.close1 c valty) valty ->
         v: t.ty_sem valty                       ->
         bigstep streams (subst1 e (XMu e)) v ->
         bigstep streams (XMu e) v

 (* Let expressions are performed by substituting into the expression.
    We could also evaluate the definition e1 to a stream of values, and add each
    of these to the stream contexts - but this is a bit easier, and later we can
    prove that they're equivalent. *)
 | BSLet:
          #b: t.ty ->
          streams: list (row c)   ->
          e1: val_exp t c b               ->
          e2: exp t (C.close1 c b) 'a
                                    ->
          v:      'a                      ->
          bigstep streams (subst1 e2 e1) v
                                    ->
          bigstep streams (XLet b e1 e2) v

 // | BSContract:
 //          streams: list (row c)   ->
 //          ea: exp ['b]    xprop ->
 //          eg: exp ['a; 'b] xprop ->
 //          eb: exp ['b]    'a     ->
 //          earg: exp c                     'b     ->
 //          v:                              'a     ->
 //          bigstep streams
 //            (subst1 (weaken c eb) earg)
 //            v                                  ->
 //          bigstep streams (XContract ea eg eb earg) v

 | BSCheck:
          streams: list (row c)   ->
          name:    string                       ->
          eprop:   val_exp t c                  t.propty ->
          e:       exp t c                      'a     ->
          v:                                    'a     ->
          bigstep streams e v                   ->
          bigstep streams (XCheck name eprop e) v


(* Under streaming history `streams`, evaluate expression `e` at each step to
   produce stream of values `vs` *)
noeq
type bigsteps (#t: table) (#c: context t) (#a: Type): list (row c) -> exp t c a -> list a -> Type =
 | BSs0:
    e: exp t c a                          ->
    bigsteps [] e []
 | BSsS:
    rows: list (row c)                ->
    e: exp t c a                          ->
    vs: list a                          ->
    row: row c                        ->
    v: a                                ->
    bigsteps        rows  e      vs     ->
    bigstep  (row :: rows) e  v          ->
    bigsteps (row :: rows) e (v :: vs)

#push-options "--split_queries always"
(* Properties *)
let rec bigstep_proof_equivalence
  (#t: table)
  (#c: context t)
  (#streams: list (row c))
  (#e: exp t c 'a)
  (#v1 #v2: 'a)
  (hBS1: bigstep streams e v1) (hBS2: bigstep streams e v2):
    Lemma (ensures hBS1 === hBS2) (decreases hBS1) =
  match hBS1 with
  | BSVal _ _  -> ()
  | BSVar _ _ _ -> ()
  | BSPrim _ _ -> ()

  | BSApp _ _ _ _ _ bs11 bs12 ->
    let BSApp _ _ _ _ _ bs21 bs22 = hBS2 in
    bigstep_proof_equivalence bs11 bs21;
    bigstep_proof_equivalence bs12 bs22

  | BSFby1 _ _ _ ->
    ()
  | BSFbyS _ _ _ _ _ bs1 ->
    let BSFbyS _ _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSThen1 _ _ _ _ bs12 ->
    let BSThen1 _ _ _ _ bs22 = hBS2 in
    bigstep_proof_equivalence bs12 bs22

  | BSThenS _ _ _ _ bs12 ->
    let BSThenS _ _ _ _ bs22 = hBS2 in
    bigstep_proof_equivalence bs12 bs22

  | BSMu _ _ _ bs1 ->
    let BSMu _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSLet _ _ _ _ bs1 ->
    let BSLet _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSCheck _ _ _ _ _ bs1 ->
    let BSCheck _ _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

let bigstep_deterministic
  (#t: table)
  (#c: context t)
  (#streams: list (row c))
  (#e: exp t c 'a)
  (#v1 #v2: 'a)
  (hBS1: bigstep streams e v1) (hBS2: bigstep streams e v2):
    Lemma (ensures (v1 == v2)) (decreases hBS1) =
  bigstep_proof_equivalence hBS1 hBS2

