module Pipit.Exp.Base

type prim2 =
  | And | Or | NAnd | Implies | Eq // | ...

let value  = bool
let var    = nat

let eval_prim2 (p: prim2) (v1 : value) (v2: value) =
  match p with
  | And  -> v1 && v2
  | Or   -> v1 || v2
  | Implies -> not v1 || v2
  | Eq -> v1 = v2

type exp =
  // v
  | XVal   : value -> exp
  // x
  | XVar   : var -> exp
  // f(e,...)
  | XPrim2 : prim2 -> exp -> exp -> exp
  // pre e
  | XPre   : exp -> exp
  // e -> e'
  | XThen  : exp -> exp -> exp
  // µx. e[x]
  | XMu    : exp -> exp

let xpre_init: value = true

let rec wf (e: exp) (n: var): prop =
match e with
| XVal _ -> True
| XVar x -> (x < n) == true
| XPrim2 _ e1 e2 -> wf e1 n /\ wf e2 n
| XPre e1 -> wf e1 n
| XThen e1 e2 -> wf e1 n /\ wf e2 n
| XMu e1 -> wf e1 (n + 1)

(* Properties *)
let rec wf_weaken (e: exp) (n: var) (n': var { n <= n' }):
  Lemma (requires wf e n)
        (ensures wf e n') =
  match e with
  | XVal _ -> ()
  | XVar x' -> ()
  | XPrim2 _ e1 e2 ->
    wf_weaken e1 n n';
    wf_weaken e2 n n'
  | XPre e1 -> wf_weaken e1 n n'
  | XThen e1 e2 ->
    wf_weaken e1 n n';
    wf_weaken e2 n n'
  | XMu e1 ->
    wf_weaken e1 (n + 1) (n' + 1)
