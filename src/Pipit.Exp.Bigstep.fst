(* Bigstep semantics for expressions.
   This is a bit different from the standard "reactive step" operational
   semantics. The reactive step semantics operate under a single environment and
   allow an expression e to step to a new expression e', producing a value. In
   contrast, the bigstep relation here takes a stream of environments, and
   fully evaluates an expression to a value.
   The bigstep semantics feels a lot more functional (applicative), while the
   reactive step semantics better matches the actual streaming execution mode.
*)
module Pipit.Exp.Bigstep

open Pipit.Exp.Base

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
           prefix: list (C.row c) { List.Tot.length prefix > 1 }
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
 | BSMu: streams: list (C.row c)    ->
         e: exp (C.bind_index1 c 'a) 'a ->
         v: 'a                       ->
         bigstep streams (subst_index1 e (XMu e)) v ->
         bigstep streams (XMu e) v

 (* Let expressions are performed by substituting into the expression.
    We could also evaluate the definition e1 to a stream of values, and add each
    of these to the stream contexts - but this is a bit easier, and later we can
    prove that they're equivalent. *)
 | BSLet: streams: list (C.row c)   ->
          e1: exp c 'b               ->
          e2: exp (C.bind_index1 c 'b) 'a
                                    ->
          v: 'a                      ->
          bigstep streams (subst_index1 e2 e1) v
                                    ->
          bigstep streams (XLet 'b e1 e2) v

 | BSContract:
          streams: list (C.row c)   ->
          ea: exp (C.from_indices ['b])    xprop ->
          eg: exp (C.from_indices ['a; 'b]) xprop ->
          eb: exp (C.from_indices ['b])    'a     ->
          earg: exp c                     'b     ->
          v:                              'a     ->
          bigstep streams
            (subst_index1 (weaken_closed c eb) earg)
            v                                  ->
          bigstep streams (XContract ea eg eb earg) v

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
let rec bigsteps (streams: list (C.row 'c)) (e: exp 'c 'a) (vs: list 'a { List.Tot.length vs == List.Tot.length streams }): prop =
  match streams, vs with
  | (t :: ts'), (v :: vs') ->
    squash (bigstep streams e v) /\ bigsteps ts' e vs'
  | [], [] ->
    True

//TODO clean
#push-options "--split_queries"
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

  | BSMu _ _ _ bs1 ->
    let BSMu _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSLet _ _ _ _ bs1 ->
    let BSLet _ _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSContract _ _ _ _ _ _ bs1 ->
    let BSContract _ _ _ _ _ _ bs2 = hBS2 in
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

(* Shelve: disable proofs. monotone will require causality  *)
(*

let rec bigstep_monotone (#outer #inner: nat)
  (#streams: C.table (outer + 1) inner) (#e: exp) (#vs: C.vector value (outer + 1))
  (hBS1: bigstep streams e vs):
    Tot (bigstep (C.table_tl streams) e (C.vector_tl vs)) (decreases hBS1) =
 match hBS1 with
 | BSVal _ v ->
   BSVal _ v
 | BSPrim2 _ p e1 e2 vs1 vs2 hBS1 hBS2 ->
   BSPrim2 _ p e1 e2 (C.vector_tl vs1) (C.vector_tl vs2)
     (bigstep_monotone hBS1)
     (bigstep_monotone hBS2)
 | BSVar _ x ->
   BSVar _ x
 | BSPre here streams' e1 vs hBS1 ->
   if outer = 0
   then BSPre0 e1
   else BSPre (C.table_hd #(outer - 1) streams') (C.table_tl streams') e1 (C.vector_tl vs) (bigstep_monotone #(outer - 1) hBS1)
 | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
   BSThen _ e1 e2 (C.vector_tl vs1) (C.vector_tl vs2)
     (bigstep_monotone hBS1)
     (bigstep_monotone hBS2)
 | BSMu _ e1 vs1 hBS1 ->
   BSMu _ e1 (C.vector_tl vs1) (bigstep_monotone hBS1)
 | BSLet _ e1 e2 vs2 hBS2 ->
   BSLet _ e1 e2 (C.vector_tl vs2) (bigstep_monotone hBS2)


(* kill? *)
let bigstep_lookup_BSVar (#outer #inner1 #inner2: nat)
  (streams1: C.table outer inner1)
  (streams2: C.table outer inner2)
  (vs: C.vector value outer):
    bigstep (C.table_map_append streams1 (C.table_map_append (C.table_of_values vs) streams2)) (XVar inner1) vs =
  let t_vs = C.table_of_values vs in
  C.table_index_table_of_values vs;
  C.table_index_append_inner1 t_vs streams2 0;
  C.table_index_append_inner2 streams1 (C.table_map_append t_vs streams2) inner1;
  BSVar _ inner1

let bigstep_contract_map_append_inner1 (#outer #inner1 #inner2: nat)
  (streams1: C.table outer inner1)
  (streams2: C.table outer inner2)
  (x: var { x < inner1 })
  (vs: C.vector value outer)
  (hBS: bigstep (C.table_map_append streams1 streams2) (XVar x) vs):
    bigstep streams1 (XVar x) vs =
 C.table_index_append_inner1 streams1 streams2 x;
 BSVar _ x

let bigstep_contract_map_append_inner2 (#outer #inner1 #inner2: nat)
  (streams1: C.table outer inner1)
  (streams2: C.table outer inner2)
  (x: var { inner1 <= x /\ x < inner1 + inner2 })
  (vs: C.vector value outer)
  (hBS: bigstep (C.table_map_append streams1 streams2) (XVar x) vs):
    bigstep streams2 (XVar (x - inner1)) vs =
  C.table_index_append_inner2 streams1 streams2 x;
  BSVar _ (x - inner1)


let rec bigstep_weaken (#outer #inner1 #inner2: nat)
  (e: exp)
  (streams1: C.table outer inner1)
  (streams2: C.table outer inner2)
  (vs: C.vector value outer)
  (hBS: bigstep streams1 e vs):
      Tot (bigstep (C.table_map_append streams1 streams2) e vs) (decreases hBS) =
 let str12 = C.table_map_append streams1 streams2 in
 match hBS with
 | BSVal _ v ->
   C.table_const_const streams1 str12 v;
   BSVal _ v
 | BSVar _ x ->
   C.table_index_append_inner1 streams1 streams2 x;
   BSVar _ x
 | BSPrim2 _ p e1 e2 vs1 vs2 hBS1 hBS2 ->
   BSPrim2 str12 p e1 e2 vs1 vs2
     (bigstep_weaken _ streams1 streams2 _ hBS1)
     (bigstep_weaken _ streams1 streams2 _ hBS2)
 | BSPre _ _ e1 vs1 hBS1 ->
   BSPre (C.table_hd #(outer - 1) str12) (C.table_tl str12) e1 vs1
     (bigstep_weaken e1 (C.table_tl streams1) (C.table_tl streams2) vs1 hBS1)
 | BSPre0 e1 -> BSPre0 e1
 | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
   BSThen str12 e1 e2 vs1 vs2
     (bigstep_weaken _ streams1 streams2 _ hBS1)
     (bigstep_weaken _ streams1 streams2 _ hBS2)
 | BSMu _ e1 vs1 hBS1 ->
   BSMu str12 e1 vs1
     (bigstep_weaken _ streams1 streams2 _ hBS1)
 | BSLet _ e1 e2 vs2 hBS2 ->
   BSLet str12 e1 e2 vs2
     (bigstep_weaken _ streams1 streams2 _ hBS2)

let bigstep_substitute__XVar_lt (#outer #inner1 #inner2: nat) (x: var { x < inner1 })
  (spre: C.table  outer inner1)
  (smid: C.table  outer 1)
  (send: C.table outer inner2)
  (vs: C.vector value outer)
  (hBS: bigstep (C.table_map_append spre (C.table_map_append smid send)) (XVar x) vs):
    Tot (bigstep (C.table_map_append spre send) (XVar x) vs) =
  let hBS' = bigstep_contract_map_append_inner1 spre (C.table_map_append smid send) x vs hBS in
  bigstep_weaken _ spre send _ hBS'

let bigstep_substitute__XVar_gt (#outer #inner1 #inner2: nat) (x: var { inner1 + 1 <= x /\ x < inner1 + 1 + inner2 })
  (spre: C.table  outer inner1)
  (smid: C.table  outer 1)
  (send: C.table outer inner2)
  (vs: C.vector value outer)
  (hBS: bigstep (C.table_map_append spre (C.table_map_append smid send)) (XVar x) vs):
    Tot (bigstep (C.table_map_append spre send) (XVar (x - 1)) vs) =
  C.table_index_append_inner2 spre (C.table_map_append smid send) x;
  C.table_index_append_inner2 smid send (x - inner1);
  C.table_index_append_inner2 spre send (x - 1);
  BSVar _ (x - 1)



// #push-options "--split_queries"
let rec bigstep_substitute (#outer #inner1 #inner2: nat) (e p: exp)
  (streams1: C.table outer inner1)
  (streams2: C.table outer inner2)
  (vse vsp: C.vector value outer)
  (hBSe: bigstep (C.table_map_append streams1 (C.table_map_append (C.table_of_values vsp) streams2)) e vse)
  (hBSp: bigstep streams1 p vsp)
    : Tot (bigstep (C.table_map_append streams1 streams2) (subst e inner1 p) vse) (decreases hBSe) =
 let str_v2 = C.table_map_append (C.table_of_values vsp) streams2 in
 let str_1v2 = C.table_map_append streams1 str_v2 in
 let str_12 = C.table_map_append streams1 streams2 in
 match hBSe with
 | BSVal _ v ->
   C.table_const_const str_1v2 str_12 v;
   BSVal _ v
 | BSVar _ x ->
    if x = inner1
    then
      let _ = bigstep_lookup_BSVar streams1 streams2 vsp in
      bigstep_weaken _ streams1 streams2 _ hBSp
    else if x < inner1
    then
      bigstep_substitute__XVar_lt x streams1 (C.table_of_values vsp) streams2 vse hBSe
    else
      bigstep_substitute__XVar_gt x streams1 (C.table_of_values vsp) streams2 vse hBSe
 | BSPrim2 _ prim e1 e2 vs1 vs2 hBS1 hBS2 ->
   let hBS1' = bigstep_substitute e1 p streams1 streams2 vs1 vsp hBS1 hBSp in
   let hBS2' = bigstep_substitute e2 p streams1 streams2 vs2 vsp hBS2 hBSp in
   BSPrim2 str_12 prim (subst e1 inner1 p) (subst e2 inner1 p) vs1 vs2 hBS1' hBS2'
 | BSPre here0 there0 e1 vs1 hBS1 ->
   let s1'   = C.table_tl #(outer - 1) streams1 in
   let s2'   = C.table_tl #(outer - 1) streams2 in
   let vsp'  = C.vector_tl #(outer - 1) vsp in
   let hBSp' = bigstep_monotone hBSp in
   let hBS1' = bigstep_substitute e1 p s1' s2' vs1 vsp' hBS1 hBSp' in
   BSPre (C.table_hd #(outer - 1) str_12) (C.table_tl str_12) (subst e1 inner1 p) vs1 hBS1'
 | BSPre0 e1 -> BSPre0 (subst e1 inner1 p)
 | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
   let hBS1' = bigstep_substitute e1 p streams1 streams2 vs1 vsp hBS1 hBSp in
   let hBS2' = bigstep_substitute e2 p streams1 streams2 vs2 vsp hBS2 hBSp in
   BSThen str_12 (subst e1 inner1 p) (subst e2 inner1 p) vs1 vs2 hBS1' hBS2'
 | BSMu _ e1 vs1 hBS1 ->
   let hBS1' = bigstep_substitute (subst e1 0 (XMu e1)) p streams1 streams2 vs1 vsp hBS1 hBSp in
   subst_subst_distribute_XMu e1 p inner1;
   BSMu str_12 (subst e1 (inner1 + 1) (lift p 0)) vs1 hBS1'
 | BSLet _ e1 e2 vs2 hBS2 -> admit ()

let rec bigstep_substitute_as_var (#outer #inner1 #inner2: nat) (e p: exp)
  (streams1: C.table outer inner1)
  (streams2: C.table outer inner2)
  (vsp vsep: C.vector value outer)
  (hBSp: bigstep (C.table_map_append streams1 streams2) p vsp)
  (hBSep: bigstep (C.table_map_append streams1 streams2) (subst e inner1 p) vsep):
    Tot (bigstep (C.table_map_append streams1 (C.table_map_append (C.table_of_values vsp) streams2)) e vsep) (decreases hBSep) =
  let str_v2  = C.table_map_append (C.table_of_values vsp) streams2 in
  let str_1v2 = C.table_map_append streams1 str_v2 in
  let str_12  = C.table_map_append streams1 streams2 in
  let assumption: bigstep str_1v2 (XVar inner1) vsp =
    C.table_index_append_inner2 streams1 str_v2 inner1;
    C.table_index_append_inner1 (C.table_of_values vsp) streams2 0;
    C.table_index_table_of_values vsp;
    BSVar _ inner1
  in
  if e = XVar inner1
  then begin
    bigstep_deterministic hBSp hBSep;
    assumption
  end
  else
  match hBSep with
  | BSVal _ v ->
    C.table_const_const str_12 str_1v2 v;
    BSVal _ v
  | BSVar _ x ->
    if x < inner1 then begin
      C.table_index_append_inner1 streams1 streams2 x;
      C.table_index_append_inner1 streams1 str_v2 x;
      BSVar _ x
    end
    else begin
      let x' = x + 1 in
      C.table_index_append_inner2 streams1 streams2 x;
      C.table_index_append_inner2 streams1 str_v2 x';
      C.table_index_append_inner2 (C.table_of_values vsp) streams2 (x' - inner1);
      BSVar _ x'
    end
  | BSPrim2 _ prim e1 e2 vs1 vs2 hBS1 hBS2 ->
    let XPrim2 _ e1' e2' = e in
    let hBS1' = bigstep_substitute_as_var e1' p streams1 streams2 vsp vs1 hBSp hBS1 in
    let hBS2' = bigstep_substitute_as_var e2' p streams1 streams2 vsp vs2 hBSp hBS2 in
    BSPrim2 _ prim e1' e2' vs1 vs2 hBS1' hBS2'
  | BSThen _ e1 e2 vs1 vs2 hBS1 hBS2 ->
    let XThen e1' e2' = e in
    let hBS1' = bigstep_substitute_as_var e1' p streams1 streams2 vsp vs1 hBSp hBS1 in
    let hBS2' = bigstep_substitute_as_var e2' p streams1 streams2 vsp vs2 hBSp hBS2 in
    BSThen _ e1' e2' vs1 vs2 hBS1' hBS2'
  | BSMu _ e1 vs1 hBS1 ->
    let XMu e1' = e in
    subst_subst_distribute_XMu e1' p inner1;
    let hBS1' = bigstep_substitute_as_var (subst e1' 0 (XMu e1')) p streams1 streams2 vsp vs1 hBSp hBS1 in
    BSMu _ e1' vs1 hBS1'
  | BSPre0 _ ->
    let XPre e1' = e in
    BSPre0 e1'
  // TODO bigstep_substitute_as_var BSPre, BSLet: looks pretty true
  | _ -> admit ()

let bigstep_substitute_XMu (#outer #inner: nat) (e: exp)
  (streams: C.table outer inner)
  (vs: C.vector value outer)
  (hBSmu: bigstep streams (XMu e) vs):
    bigstep (C.table_map_append (C.table_of_values vs) streams) e vs =
  C.table_map_append_empty1 (C.table_map_append (C.table_of_values vs) streams);
  C.table_map_append_empty1 streams;
  let BSMu _ _ _ hBS' = hBSmu in
  bigstep_substitute_as_var e (XMu e) (C.table_empty outer) streams vs vs hBSmu hBS'



*)
