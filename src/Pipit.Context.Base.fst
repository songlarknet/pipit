(* Binding contexts: helpers for indexing into lists. *)
module Pipit.Context.Base

module List = FStar.List.Tot


type var (#ty: eqtype) (t: ty) =
  (* Keep constructor so "var int" is different from "var string" *)
  | Var: (v: nat) -> var t

let var_eq (#ty: eqtype) (#a #b: ty) (x: var a) (x': var b):
  (eq: bool { eq <==> x === x' }) =
  if a = b then x = x' else false


type context 'a = list 'a
type context_t = context eqtype

let index  = nat
let index_lookup (c: context 'a) = i: index { i <  List.length c }
let index_insert (c: context 'a) = i: index { i <= List.length c }

let context_sem (typ_sem: 'a -> eqtype) (c: context 'a): context_t = List.map typ_sem c

let has_index (c: context 'a) (i: index) = i < List.length c
let get_index (c: context 'a) (i: index_lookup c): 'a = List.index c i
let opt_index (c: context 'a) (i: index): option 'a = if has_index c i then Some (get_index c i) else None

let empty = []

let append (c c': context 'a): context 'a = List.append c c'

let rec drop1 (l: context 'a) (i: index_lookup l): (l': context 'a { List.length l' == List.length l - 1 }) =
  match l, i with
  | _ :: l', 0 -> l'
  | l0 :: l', _ -> l0 :: drop1 l' (i - 1)

let rec lift1 (l: context 'a) (i: index_insert l) (v: 'a): (l': context 'a { List.length l' == List.length l + 1 }) =
  match l, i with
  | _, 0 -> v :: l
  | l0 :: l', _ -> l0 :: lift1 l' (i - 1) v

let index_drop (i limit: index): (r: index { (i > limit ==> r = i - 1) /\ (i <= limit ==> r = i )}) =
  if i > limit then i - 1 else i

let index_lift (i limit: index): (r: index { (i >= limit ==> r = i + 1) /\ (i < limit ==> r = i) }) =
  if i >= limit then i + 1 else i

let open1' (c: context 'a) (i: index_lookup c): context 'a = drop1 c i
let open1 (c: context 'a { has_index c 0 }): context 'a = List.tl c

let close1' (c: context 'a) (t: 'a) (i: index_insert c): context 'a = lift1 c i t
let close1 (c: context 'a) (t: 'a): context 'a = t :: c
