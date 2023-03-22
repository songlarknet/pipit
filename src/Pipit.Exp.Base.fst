module Pipit.Exp.Base

type prim2 =
  | AndB | OrB | ImpliesB
  | EqZ
  | AddZ | SubZ | LeZ // | ...

let value  = int
let var    = nat

let bool_of_value (v: value): bool = v <> 0
let value_of_bool (b: bool): value = if b then 1 else 0

let eval_prim2 (p: prim2) (v1 : value) (v2: value): value =
  match p with
  | AndB     -> value_of_bool (bool_of_value v1 && bool_of_value v2)
  | OrB      -> value_of_bool (bool_of_value v1 || bool_of_value v2)
  | ImpliesB -> if bool_of_value v1 then v2 else 1
  | EqZ      -> value_of_bool (v1 = v2)
  | AddZ     -> v1 + v2
  | SubZ     -> v1 - v2
  | LeZ      -> value_of_bool (v1 <= v2)

type exp =
  // v
  | XVal   : value -> exp
  // x
  | XVar   : var -> exp
  // f(e,...)
  | XPrim2 : prim2 -> exp -> exp -> exp
  // if p then e else e'
  | XIte   : exp -> exp -> exp -> exp
  // pre e
  | XPre   : exp -> exp
  // e -> e'
  | XThen  : exp -> exp -> exp
  // µx. e[x]
  | XMu    : exp -> exp
  // let x = e in e[x]
  | XLet   : exp -> exp -> exp


let rec wf (e: exp) (n: var): prop =
match e with
| XVal _ -> True
| XVar x -> (x < n) == true
| XPrim2 _ e1 e2 -> wf e1 n /\ wf e2 n
| XIte ep et ef -> wf ep n /\ wf et n /\ wf ef n
| XPre e1 -> wf e1 n
| XThen e1 e2 -> wf e1 n /\ wf e2 n
| XMu e1 -> wf e1 (n + 1)
| XLet e1 e2 -> wf e1 n /\ wf e2 (n + 1)

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
  | XIte ep e1 e2 ->
    wf_weaken ep n n';
    wf_weaken e1 n n';
    wf_weaken e2 n n'
  | XPre e1 -> wf_weaken e1 n n'
  | XThen e1 e2 ->
    wf_weaken e1 n n';
    wf_weaken e2 n n'
  | XMu e1 ->
    wf_weaken e1 (n + 1) (n' + 1)
  | XLet e1 e2 ->
    wf_weaken e1 n n';
    wf_weaken e2 (n + 1) (n' + 1)


let xpre_init: value = 0
