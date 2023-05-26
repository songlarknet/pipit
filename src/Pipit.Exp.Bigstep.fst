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

open Pipit.Exp.Base
open Pipit.Exp.Binding
open Pipit.Inhabited

module C = Pipit.Context

(* bigstep streams e v

 Bigstep semantics: in streaming history `streams`, which is a 2-dimensional table of
 `elts` elements and `vars` variables, the expression `e` evaluates to value `v`.
 The stream history `streams` is in most-recent-first order.
 *)
noeq
type bigstep (#c: C.context): (#a: Type) -> list (C.row c) -> exp c a -> a -> Type =
 (* Values `v` always evaluate to the value *)
 | BSVal:
          streams: list (C.row c) ->
          v: 'a ->
          bigstep streams (XVal v) v

 (* Variables `x` are looked up in the most recent row in the stream history *)
 | BSVar: latest: C.row c ->
          prefix: list (C.row c) ->
          x: C.index { C.has_index c x } ->
          bigstep (latest :: prefix) (XBVar x) (C.row_index c latest x)

 (* Element-wise application *)
 | BSApp: streams: list (C.row c) ->
          f: exp c ('a -> 'b)        ->
          e: exp c  'a             ->
          f_v: ('a -> 'b)            ->
          e_v:  'a                 ->
          bigstep streams f f_v   ->
          bigstep streams e e_v   ->
          bigstep streams (XApp f e) (f_v e_v)

 (* To compute `pre e` we evaluate `e` without the most recent element. *)
 | BSFby1: start: list (C.row c) { List.Tot.length start <= 1 }
                                    ->
           v0: 'a                    ->
           e: exp c 'a               ->
           bigstep start (XFby v0 e) v0
 (* To compute `pre e` we evaluate `e` without the most recent element. *)
 | BSFbyS: latest: C.row c          ->
           prefix: list (C.row c) { List.Tot.length prefix >= 1 }
                                    ->
           v0: 'a                    ->
           v': 'a                    ->
           e: exp c 'a               ->
           bigstep           prefix           e  v' ->
           bigstep (latest :: prefix) (XFby v0 e) v'

 (* First step of (p -> q) is p *)
 | BSThen1: start: list (C.row c) { List.Tot.length start <= 1 }
                                    ->
            e1: exp c 'a             ->
            e2: exp c 'a             ->
            v: 'a                    ->
            bigstep start        e1     v ->
            bigstep start (XThen e1 e2) v
 (* Subsequent steps of (p -> q) are q *)
 | BSThenS: streams: list (C.row c) { List.Tot.length streams > 1 }
                                    ->
            e1: exp c 'a             ->
            e2: exp c 'a             ->
            v: 'a                    ->
            bigstep streams           e2  v ->
            bigstep streams (XThen e1 e2) v

 (* Reduction for recursive expressions proceeds by unfolding the recursion one step.
    If all recursive references are guarded by `pre` then the `pre` step will look
    at a shorter stream history prefix, and should eventually terminate. *)
 | BSMu: (i: inhabited 'a) ->
         streams: list (C.row c)    ->
         e: exp (C.close1 c 'a) 'a ->
         v: 'a                       ->
         bigstep streams (subst1 e (XMu e)) v ->
         bigstep streams (XMu e) v

 (* Let expressions are performed by substituting into the expression.
    We could also evaluate the definition e1 to a stream of values, and add each
    of these to the stream contexts - but this is a bit easier, and later we can
    prove that they're equivalent. *)
 | BSLet: streams: list (C.row c)   ->
          e1: exp c 'b               ->
          e2: exp (C.close1 c 'b) 'a
                                    ->
          v: 'a                      ->
          bigstep streams (subst1 e2 e1) v
                                    ->
          bigstep streams (XLet 'b e1 e2) v

 // | BSContract:
 //          streams: list (C.row c)   ->
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
          streams: list (C.row c)   ->
          name:    string                       ->
          eprop:   exp c                  xprop ->
          e:       exp c                  'a     ->
          v:                              'a     ->
          bigstep streams e v                   ->
          bigstep streams (XCheck name eprop e) v


(* Under streaming history `streams`, evaluate expression `e` at each step to
   produce stream of values `vs` *)
noeq
type bigsteps (#c: C.context) (#a: Type): list (C.row c) -> exp c a -> list a -> Type =
 | BSs0:
    e: exp c a                          ->
    bigsteps [] e []
 | BSsS:
    rows: list (C.row c)                ->
    e: exp c a                          ->
    vs: list a                          ->
    row: C.row c                        ->
    v: a                                ->
    bigsteps        rows  e      vs     ->
    bigstep  (row :: rows) e  v          ->
    bigsteps (row :: rows) e (v :: vs)

#push-options "--split_queries always"
(* Properties *)
let rec bigstep_proof_equivalence
  (#streams: list (C.row 'c))
  (#e: exp 'c 'a)
  (#v1 #v2: 'a)
  (hBS1: bigstep streams e v1) (hBS2: bigstep streams e v2):
    Lemma (ensures hBS1 === hBS2) (decreases hBS1) =
  match hBS1 with
  | BSVal _ _  -> ()
  | BSVar _ _ _ -> ()

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

  | BSMu _ _ _ _ bs1 ->
    let BSMu _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSLet _ _ _ _ bs1 ->
    let BSLet _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSCheck _ _ _ _ _ bs1 ->
    let BSCheck _ _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

let bigstep_deterministic
  (#streams: list (C.row 'c))
  (#e: exp 'c 'a)
  (#v1 #v2: 'a)
  (hBS1: bigstep streams e v1) (hBS2: bigstep streams e v2):
    Lemma (ensures (v1 == v2)) (decreases hBS1) =
  bigstep_proof_equivalence hBS1 hBS2

