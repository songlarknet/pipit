module Pipit.Exp.Bigstep

open Pipit.Exp.Base
open Pipit.Exp.Subst

module C = Pipit.Context

(* Semantics of then (->) on lists. The lists are in most-recent-first order. *)
let rec then_ (#n: nat) (#a: Type)
  (l1: C.vector a n) (l2: C.vector a n):
   C.vector a n =
  match l1, l2 with
  | [], [] -> []
  | [v], [_] -> [v]
  | _ :: l1', v :: l2' -> v :: then_ #(n - 1) l1' l2'

(* bigstep streams e vs

 Bigstep semantics: in streaming history `streams`, which is a 2-dimensional table of
 `outer` elements and `inner` variables, the expression `e` evaluates to `vs`, which
 is a vector of values with one value for each `outer` element.
 The stream history `streams` and values `vs` are in most-recent-first order.
 *)
noeq type bigstep (#inner: nat): (#outer: nat) -> C.table outer inner -> exp -> C.vector value outer -> Type =
 (* Values `v` always evaluate to the value *)
 | BSVal: #outer: nat ->
          streams: C.table outer inner -> v: value ->
          bigstep streams (XVal v) (C.table_const streams v)
 (* Variables `x` are looked up in the stream history *)
 | BSVar: #outer: nat ->
          streams: C.table outer inner -> x: var { x < inner } ->
          bigstep streams (XVar x) (C.table_index streams x)
 (* Primitives are applied element-wise to the stream *)
 | BSPrim2: #outer: nat ->
            streams: C.table outer inner -> p: prim2 -> e1: exp -> e2: exp ->
            vs1: C.vector value outer ->
            vs2: C.vector value outer ->
            bigstep streams e1 vs1 ->
            bigstep streams e2 vs2 ->
            bigstep streams (XPrim2 p e1 e2) (C.vector_map2 (eval_prim2 p) vs1 vs2)
 (* To compute `pre e` we evaluate `e` without the last element.
   We arbitrarily define `pre e = true -> ...` so that the core logic is deterministic.
   *)
 | BSPre: #outer: nat ->
          here: C.row inner -> streams: C.table outer inner ->
          e: exp -> vs: C.vector value outer ->
          bigstep streams e vs ->
          bigstep (C.table_append (C.table1 here) streams) (XPre e) (C.vector_append vs (C.vector1 xpre_init))
 (* All causal expressions should evaluate to empty in the empty context, but the above
   rule for pre doesn't fit, so we add a special rule. We could add a more general rule
   that says `forall e. bigstep [] e []`, but such a rule would make the relation less
   syntax-directed and complicate some of the proofs. *)
 | BSPre0: e: exp ->
           bigstep (C.Table #0 #inner []) (XPre e) []
 (* Then or (e1 -> e2) is defined using then_, which is basically `hd e1 :: tl e2` *)
 | BSThen: #outer: nat ->
           streams: C.table outer inner -> e1: exp -> e2: exp ->
           vs1: C.vector value outer ->
           vs2: C.vector value outer ->
           bigstep streams e1 vs1 ->
           bigstep streams e2 vs2 ->
           bigstep streams (XThen e1 e2) (then_ vs1 vs2)
 (* Reduction for recursive expressions proceeds by unfolding the recursion one step.
    If all recursive references are guarded by `pre` then the `pre` step will look
    at a shorter stream history prefix, and should eventually terminate. *)
 | BSMu: #outer: nat ->
         streams: C.table outer inner -> e: exp ->
         vs: C.vector value outer ->
         bigstep streams (subst e 0 (XMu e)) vs ->
         bigstep streams (XMu e) vs

(* Inversion rules:
  these look trivial, but it seems that the solver can't always figure them out
  inside a larger expression. *)
let invert_BSVal (#outer #inner: nat)
  (h: C.table outer inner) (e: exp) (vs: C.vector value outer)
  (bs: bigstep h e vs { BSVal? bs }):
    Lemma (exists (v: value). vs == C.table_const h v) = ()

let invert_BSVar (#outer #inner: nat)
  (h: C.table outer inner) (e: exp) (vs: C.vector value outer)
  (bs: bigstep h e vs { BSVar? bs }):
    Lemma (exists (x: var { x < inner }). vs == C.table_index h x) = ()

let invert_BSPre (#outer #inner: nat)
  (h: C.table outer inner) (e: exp) (vs: C.vector value outer)
  (bs: bigstep h e vs { BSPre? bs }):
    Lemma (exists (vs': C.vector value (outer - 1)). vs == C.vector_append vs' (C.vector1 true)) = ()

let invert_BSThen (#outer #inner: nat)
  (h: C.table outer inner) (e: exp) (vs: C.vector value outer)
  (bs: bigstep h e vs { BSThen? bs }):
    Lemma (exists (vs1 vs2: C.vector value outer). vs == then_ vs1 vs2) = ()

(* Properties *)
let rec bigstep_deterministic (#outer #inner: nat)
  (#streams: C.table outer inner) (#e: exp)
  (#vs1 #vs2: C.vector value outer)
  (hBS1: bigstep streams e vs1) (hBS2: bigstep streams e vs2):
    Lemma (ensures (vs1 = vs2)) (decreases hBS1) =
  match hBS1 with
  | BSVal _ _  -> ()
  | BSVar _ _ -> ()

  | BSPrim2 _ _ _ _ _ _ bs11 bs12 ->
    let BSPrim2 _ _ _ _ _ _ bs21 bs22 = hBS2 in
    bigstep_deterministic bs11 bs21;
    bigstep_deterministic bs12 bs22

  | BSPre here1' streams1' _ _ bs1 ->
    let BSPre here2' streams2' _ _ bs2 = hBS2 in
    C.table_append_injective streams1' streams2' (C.table1 here1') (C.table1 here2');
    bigstep_deterministic bs1 bs2

  | BSPre0 _ -> ()

  | BSThen _ _ _ _ _ bs11 bs12 ->
    let BSThen _ _ _ _ _ bs21 bs22 = hBS2 in
    bigstep_deterministic bs11 bs21;
    bigstep_deterministic bs12 bs22

  | BSMu _ _ _ bs1 ->
    let BSMu _ _ _ bs2 = hBS2 in
    bigstep_deterministic bs1 bs2

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

let rec bigstep_proof_equivalence (#outer #inner: nat)
  (#streams: C.table outer inner) (#e: exp)
  (#vs1 #vs2: C.vector value outer)
  (hBS1: bigstep streams e vs1) (hBS2: bigstep streams e vs2):
    Lemma (ensures (hBS1 === hBS2)) (decreases hBS1) =
  match hBS1 with
  | BSVal _ _  -> ()
  | BSVar _ _ -> ()

  | BSPrim2 _ _ _ _ _ _ bs11 bs12 ->
    let BSPrim2 _ _ _ _ _ _ bs21 bs22 = hBS2 in
    bigstep_proof_equivalence bs11 bs21;
    bigstep_proof_equivalence bs12 bs22

  | BSPre here1' streams1' _ _ bs1 ->
    let BSPre here2' streams2' _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2

  | BSPre0 _ -> ()

  | BSThen _ _ _ _ _ bs11 bs12 ->
    let BSThen _ _ _ _ _ bs21 bs22 = hBS2 in
    bigstep_proof_equivalence bs11 bs21;
    bigstep_proof_equivalence bs12 bs22

  | BSMu _ _ _ bs1 ->
    let BSMu _ _ _ bs2 = hBS2 in
    bigstep_proof_equivalence bs1 bs2


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
  | BSMu _ e1 vs1 hBS1 ->
    let XMu e1' = e in
    subst_subst_distribute_XMu e1' p inner1;
    let hBS1' = bigstep_substitute_as_var (subst e1' 0 (XMu e1')) p streams1 streams2 vsp vs1 hBSp hBS1 in
    BSMu _ e1' vs1 hBS1'
  | BSPre0 _ ->
    let XPre e1' = e in
    BSPre0 e1'
  // TODO BSThen, BSPre
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


