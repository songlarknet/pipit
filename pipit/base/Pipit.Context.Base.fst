(* Binding contexts: helpers for indexing into lists. *)
module Pipit.Context.Base

module List = FStar.List.Tot


(* Specify universe to ensure type injectivity *)
type var (#ty: Type u#a) (t: ty): Type u#a =
  (* Keep constructor so "var int" is different from "var string" *)
  | Var: (v: nat) -> var t

let var_eq (#ty: eqtype) (#a #b: ty) (x: var a) (x': var b):
  (eq: bool { eq <==> x === x' }) =
  if a = b then x = x' else false


type context 'a = list 'a

let index  = nat
let index_lookup (c: context 'a) = i: index { i <  List.length c }
let index_insert (c: context 'a) = i: index { i <= List.length c }

let has_index (c: context 'a) (i: index) = i < List.length c
let get_index (c: context 'a) (i: index_lookup c): 'a = List.index c i
let opt_index (c: context 'a) (i: index): option 'a = if has_index c i then Some (get_index c i) else None

let empty = []

let append_length_plus (c c': context 'a): Lemma (List.length (List.append c c') = List.length c + List.length c') =
  // TODO PROVE EASY
  admit ()

let append (c c': context 'a): r: context 'a { List.length r = List.length c + List.length c'} =
  append_length_plus c c';
  List.append c c'

let rev_acc (c c': context 'a): context 'a = List.rev_acc c c'

let rec drop1 (l: context 'a) (i: index_lookup l): (l': context 'a { List.length l' == List.length l - 1 }) =
  match l, i with
  | _ :: l', 0 -> l'
  | l0 :: l', _ -> l0 :: drop1 l' (i - 1)

let rec lift1 (l: context 'a) (i: index_insert l) (v: 'a): (l': context 'a { List.length l' == List.length l + 1 }) =
  match l, i with
  | _, 0 -> v :: l
  | l0 :: l', _ -> l0 :: lift1 l' (i - 1) v

let rec lifts (l: context 'a) (i: index_insert l) (l': context 'a): (r: context 'a { List.length r == List.length l + List.length l' }) =
  match l, i with
  | _, 0 -> append l' l
  | l0 :: l, _ -> l0 :: lifts l (i - 1) l'

let index_drop (i limit: index): (r: index { (i > limit ==> r = i - 1) /\ (i <= limit ==> r = i )}) =
  if i > limit then i - 1 else i

let index_lift (i limit: index): (r: index { (i >= limit ==> r = i + 1) /\ (i < limit ==> r = i) }) =
  if i >= limit then i + 1 else i

let index_lifts (i limit: index) (lift_by: nat): (r: index { (i >= limit ==> r = i + lift_by) /\ (i < limit ==> r = i ) })=
  if i >= limit then i + lift_by else i

let open1' (c: context 'a) (i: index_lookup c): context 'a = drop1 c i
let open1 (c: context 'a { has_index c 0 }): context 'a = List.tl c

let close1' (c: context 'a) (t: 'a) (i: index_insert c): context 'a = lift1 c i t
let close1 (c: context 'a) (t: 'a): context 'a = t :: c
