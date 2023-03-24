(* Reactive step semantics, similar to other Lustre semantics. *)
module Pipit.Exp.ReactiveStep

open Pipit.Exp.Base
open Pipit.Exp.Subst

module C = Pipit.Context

let xBOTTOM = 0

(* Reactive semantics:
    react store e v e'
   Under given heap, expression e produces value v and steps to e'
 *)
noeq type react (#inner: nat) (store: C.row inner): exp -> value -> exp -> Type =
 | RVal: v: value ->
         react store (XVal v) v (XVal v)

 | RVar: x: var { x < inner } ->
         react store (XVar x) (C.row_index store x) (XVar x)

 | RPrim2: p: prim2 ->
        e1:  exp   -> e2:  exp   ->
        v1:  value -> v2:  value ->
        e1': exp   -> e2': exp   ->
        react store e1 v1 e1' ->
        react store e2 v2 e2' ->
        react store (XPrim2 p e1 e2) (eval_prim2 p v1 v2) (XPrim2 p e1' e2')

 | RIte:
        ep:  exp   -> e1:  exp   -> e2:  exp   ->
        vp:  value -> v1:  value -> v2:  value ->
        ep': exp   -> e1': exp   -> e2': exp   ->
        react store ep vp ep' ->
        react store e1 v1 e1' ->
        react store e2 v2 e2' ->
        react store (XIte ep e1 e2) (if vp <> 0 then v1 else v2) (XIte ep e1' e2')

 | RPre: e1: exp -> v1: value -> e1': exp ->
         react store e1 v1 e1' ->
         react store (XPre e1) xBOTTOM (XThen (XVal v1) (XPre e1))

 | RThen:
        e1:  exp   -> e2:  exp   ->
        v1:  value -> v2:  value ->
        e1': exp   -> e2': exp   ->
        react store e1 v1 e1' ->
        react store e2 v2 e2' ->
        react store (XThen e1 e2) v1 e2'

 | RLet:
        e1:  exp   -> e2:  exp   ->
        v1:  value -> v2:  value ->
        e1': exp   -> e2': exp   ->
        react store e1 v1 e1' ->
        react (C.row_append (C.row1 v1) store) e2 v2 e2' ->
        react store (XLet e1 e2) v2 (XLet e1' e2')

 | RMu:
        e1:  exp   ->
        v1:  value ->
        e1': exp   ->
        react (C.row_append (C.row1 v1) store) e1 v1 e1' ->
        react store (XMu e1) v1 (XMu e1')
