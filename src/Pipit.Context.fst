module Pipit.Context

module Map = FStar.FiniteMap.Base
module List = FStar.List.Tot


type var (t: Type) =
  (* Keep constructor so "var int" is different from "var string" ? *)
  | Var: (v: nat) -> var t
let index  = nat

(* HACK: AXIOM: assume that all fresh name allocation doesn't reuse names!
   We can't use decidable equality on two variables of different type variables
   (x: var 'a) and (x': var 'b) because equality on Type isn't decidable.
 *)
let axiom_variables_assume_global (x: var 'a) (x': var 'b { Var?.v x = Var?.v x' }): Lemma ('a == 'b) =
  admit ()

let var_eq (x: var 'a) (x': var 'b):
  (eq: bool { eq <==> x === x' }) =
  if Var?.v x = Var?.v x'
  then (axiom_variables_assume_global x x'; true)
  else false


type context = list Type

let has_index (c: context) (i: index) = i < List.length c
let get_index (c: context) (i: index { has_index c i }): Type = List.index c i
let opt_index (c: context) (i: index): option Type = if has_index c i then Some (get_index c i) else None

let empty = []

let append (c c': context): context = List.append c c'

let rec row (l: list Type): Type =
  match l with
  | [] -> unit
  | t :: ts -> t * row ts

let rec row_index (l: list Type) (r: row l) (i: index { i < List.length l }): List.index l i =
  match l with
  | t :: ts ->
    let r': t * row (List.tl l) = r in
    match r' with
    | (r0, rs) ->
      if i = 0
      then r0
      else (
        // Why coerce required?
        let res: List.index ts (i - 1) = row_index ts rs (i - 1) in
        coerce_eq #_ #(List.index l i) () res)

let rec drop1 (l: list 'a) (i: nat { i < List.length l }): (l': list 'a { List.length l' == List.length l - 1 }) =
  match l, i with
  | _ :: l', 0 -> l'
  | l0 :: l', _ -> l0 :: drop1 l' (i - 1)

let rec lift1 (l: list 'a) (i: nat { i <= List.length l }) (v: 'a): (l': list 'a { List.length l' == List.length l + 1 }) =
  match l, i with
  | _, 0 -> v :: l
  | l0 :: l', _ -> l0 :: lift1 l' (i - 1) v

let index_drop (i limit: index) (drop_by: nat { drop_by <= limit + 1 }): index =
  if i > limit then i - drop_by else i

let index_lift (i limit: index) (lift_by: nat): index =
  if i >= limit then i + lift_by else i

let open1' (c: context) (i: index { has_index c i }): context = drop1 c i
let open1 (c: context { has_index c 0 }): context = open1' c 0

let close1' (c: context) (t: Type) (i: index { i <= List.length c }): context = lift1 c i t
let close1 (c: context) (t: Type): context = close1' c t 0

// let lemma_drop0 (c: context { List.length c > 0 }) (t: Type):
//   Lemma (ensures (drop1 c 0 == List.tl c)) = ()

// let lemma_lift0 (c: context) (t: Type):
//   Lemma (ensures (lift1 c 0 t == t :: c)) = ()

// let lemma_dropS (c0: Type) (c': context) (i: index { 0 < i /\ i <= List.length c' }):
//   Lemma (ensures (drop1 (c0 :: c') i == c0 :: drop1 c' (i - 1))) = ()

// let lemma_liftS (c0: Type) (c': context) (i: index { 0 < i /\ i <= List.length c' + 1}) (t: Type):
//   Lemma (ensures (lift1 (c0 :: c') i t == c0 :: lift1 c' (i - 1) t)) = ()

// let lemma_drop_length (c: context) (i: index { has_index c i }):
//   Lemma (ensures List.length (drop1 c i) == List.length c - 1) = ()

// let lemma_lift_length (c: context) (i: index { has_index c i }) (t: Type):
//   Lemma (ensures List.length (lift1 c i t) == List.length c + 1) = ()

let rec lemma_open_preserves_opt_index (c: context) (n: index { has_index c n }) (i: index { i <> n }): Lemma (opt_index c i == opt_index (open1' c n) (index_drop i n 1)) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0 && i > 0
    then lemma_open_preserves_opt_index c' (n - 1) (i - 1)
    else ()

let rec lemma_close_preserves_opt_index (c: context) (t: Type) (n: index { n <= List.length c }) (i: index): Lemma (opt_index c i == opt_index (close1' c t n) (index_lift i n 1)) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0 && i > 0
    then lemma_close_preserves_opt_index c' t (n - 1) (i - 1)
    else ()

let rec lemma_close_contains (c: context) (t: Type) (n: index { n <= List.length c }): Lemma (opt_index (close1' c t n) n == Some t) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0
    then lemma_close_contains c' t (n - 1)
    else ()

let rec lemma_append_preserves_opt_index (c c': context) (n: index { has_index c n }): Lemma (opt_index c n == opt_index (append c c') n) =
  match c with
  | [] -> ()
  | _ :: c1' ->
    if n > 0
    then lemma_append_preserves_opt_index c1' c' (n - 1)
    else ()

let rec lemma_lift_lift_commute (c: context) (i1: index { has_index c i1 }) (i2: index { i2 <= i1 }) (t1 t2: Type):
  Lemma (ensures lift1 (lift1 c i1 t1) i2 t2 == lift1 (lift1 c i2 t2) (i1 + 1) t1) =
  match c with
  | [] -> ()
  | c0 :: c' ->
    if i2 > 0
    then (lemma_lift_lift_commute c' (i1 - 1) (i2 - 1) t1 t2;
      assert (lift1 (lift1 c' (i1 - 1) t1) (i2 - 1) t2 == lift1 (lift1 c' (i2 - 1) t2) i1 t1);
      assert (lift1 (lift1 (c0 :: c') i1 t1) i2 t2 == lift1 (lift1 (c0 :: c') i2 t2) (i1 + 1) t1);
      ())
    else ()

let rec lemma_drop_lift_eq (c: context) (i: index { i <= List.length c }) (t: Type):
  Lemma (ensures drop1 (lift1 c i t) i == c) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i > 0
    then lemma_drop_lift_eq c' (i - 1) t
    else ()

let rec lemma_lift_drop_commute_le (c: context) (i1: index { has_index c i1 }) (i2: index { i2 <= i1 }) (t: Type):
  Lemma (ensures (lift1 (drop1 c i1) i2 t == drop1 (lift1 c i2 t) (i1 + 1))) =
  match c with
  | [] -> ()
  | c0 :: c' ->
    if i1 > 0
    then 
      if i2 > 0
      then
        lemma_lift_drop_commute_le c' (i1 - 1) (i2 - 1) t
      else ()
    else ()

let rec lemma_lift_get_index (c: context) (i: index { i <= List.length c }) (t: Type):
  Lemma (ensures get_index (lift1 c i t) i == t) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i > 0
    then lemma_lift_get_index c' (i - 1) t
    else ()

let rec lemma_lift_get_index_gt (c: context) (i1: index { has_index c i1 }) (i2: index { i2 <= i1 }) (t2: Type):
  Lemma (ensures get_index (lift1 c i2 t2) (i1 + 1) == get_index c i1) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i2 > 0
    then
      lemma_lift_get_index_gt c' (i1 - 1) (i2 - 1) t2
    else ()
