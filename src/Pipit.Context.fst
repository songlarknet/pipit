module Pipit.Context

module Map = FStar.FiniteMap.Base
module List = FStar.List.Tot


let var    = nat
let index  = nat

noeq
type context = { free: Map.map var Type; bound: list Type }

let closed = (c: context { c.free == Map.emptymap })

let has_var   (c: context) (x: var)   = Map.mem x c.free
let has_index (c: context) (i: index) = i < List.length c.bound

let get_var   (c: context) (x: var { has_var c x }): Type = Map.lookup x c.free
let get_index (c: context) (i: index { has_index c i }): Type = List.index c.bound i

let opt_var   (c: context) (x: var): option Type = if has_var c x then Some (get_var c x) else None
let opt_index (c: context) (i: index): option Type = if has_index c i then Some (get_index c i) else None

let fresh     (c: context) (x: var) = ~ (has_var c x)

let empty = { free = Map.emptymap; bound = [] }
let from_indices (l: list Type): closed = { free = Map.emptymap; bound = l }

let append_closed (c c': closed): closed =
  { free = c.free; bound = List.append c.bound c'.bound }

let rec row_values (l: list Type): Type =
  match l with
  | [] -> unit
  | t :: ts -> t * row_values ts

let row (c: closed): Type = row_values c.bound

let rec row_index' (l: list Type) (r: row_values l) (i: index { i < List.length l }): List.index l i =
  match l with
  | t :: ts ->
    let r': t * row_values (List.tl l) = r in
    match r' with
    | (r0, rs) ->
      if i = 0
      then r0
      else (
        // Why coerce required?
        let res: List.index ts (i - 1) = row_index' ts rs (i - 1) in
        coerce_eq #_ #(List.index l i) () res)

let row_index (c: closed) (r: row c) (i: index { i < List.length c.bound }): List.index c.bound i =
  row_index' c.bound r i


let list_drop1 (l: list 'a) (i: nat { i < List.length l }): list 'a =
  let open List in
  let (pre, post) = splitAt i l in
  match post with
  | _ :: post' -> pre @ post'
  | _ -> pre @ post

let list_lift1 (l: list 'a) (i: nat { i <= List.length l }) (v: 'a): (l': list 'a { List.length l' == List.length l + 1 }) =
  let open List in
  let (pre, post) = splitAt i l in
  List.lemma_splitAt_snd_length i l;
  // TODO
  assume (List.length pre + List.length post = List.length l);
  List.Tot.Properties.append_length pre (v :: post);
  pre @ v :: post

let index_drop (i limit: index) (drop_by: nat { drop_by <= limit + 1 }): index =
  if i > limit then i - drop_by else i

let index_lift (i limit: index) (lift_by: nat): index =
  if i >= limit then i + lift_by else i

let open1' (c: context) (x: var { fresh c x }) (i: index { has_index c i }): context =
  { free = Map.insert x (List.index c.bound i) c.free; bound = list_drop1 c.bound i }

let open1 (c: context { has_index c 0 }) (x: var { fresh c x }): context =
  open1' c x 0

let close1' (c: context) (x: var { has_var c x }) (i: index { i <= List.length c.bound }): context =
  { free = Map.remove x c.free; bound = list_lift1 c.bound i (get_var c x) }

let close1 (c: context) (x: var { has_var c x }): context =
  close1' c x 0

let drop_var1 (c: context) (x: var { has_var c x }): context =
  { free = Map.remove x c.free; bound = c.bound }

let drop_index1 (c: context) (i: index { has_index c i }): context =
  let open List in
  { free = c.free; bound = list_drop1 c.bound i }

let bind_var1 (c: context) (x: var { fresh c x }) (t: Type): context =
  let open List in
  { free = Map.insert x t c.free; bound = t :: c.bound }

let bind_index1' (c: context) (i: index { i <= List.length c.bound }) (t: Type): context =
  let open List in
  { free = c.free; bound = list_lift1 c.bound i t }

let bind_index1 (c: context) (t: Type): context =
  let open List in
  { free = c.free; bound = t :: c.bound }

let append_preserves_opt_index_lemma (c c': closed) (n: index { has_index c n }): Lemma (opt_index c n == opt_index (append_closed c c') n) =
  admit ()

let open_preserves_opt_index_lemma (c: context) (x: var { fresh c x }) (n: index { has_index c n }) (i: index { i <> n }): Lemma (opt_index c i == opt_index (open1' c x n) (index_drop i n 1)) =
  admit ()

let open_preserves_opt_var_lemma (c: context) (x: var { fresh c x }) (n: index { has_index c n }) (x': var { x <> x' }): Lemma (opt_var c x' == opt_var (open1' c x n) x') =
  admit ()

let open_contains_opt_var_lemma (c: context) (x: var { fresh c x }) (n: index { has_index c n }): Lemma (opt_index c n == opt_var (open1' c x n) x) =
  admit ()

let close_preserves_opt_index_lemma (c: context) (x: var { has_var c x }) (n: index { n <= List.length c.bound }) (i: index): Lemma (opt_index c i == opt_index (close1' c x n) (index_lift i n 1)) =
  admit ()

let close_preserves_opt_var_lemma (c: context) (x: var { has_var c x }) (n: index { n <= List.length c.bound }) (x': var { x <> x' }): Lemma (opt_var c x' == opt_var (close1' c x n) x') =
  admit ()

let close_opt_var_contains_lemma (c: context) (x: var { has_var c x }) (n: index { n <= List.length c.bound }): Lemma (opt_index (close1' c x n) n == opt_var c x) =
  admit ()

let bind_index_preserves_opt_index_lemma (c: context) (n: index { n <= List.length c.bound }) (i: index) (t: Type): Lemma (opt_index (bind_index1' c n t) (index_lift i n 1) == opt_index c i) =
  admit ()

let drop_index_preserves_opt_index_lemma (c: context) (n: index { has_index c n }) (i: index { i <> n }): Lemma (opt_index c i == opt_index (drop_index1 c n) (index_drop i n 1)) =
  admit ()

// let bind_index_commute' (c: context) (n: index { n <= List.length c.bound }) (n': index { n' <= List.length c.bound }) (t t': Type): Lemma (bind_index1' (bind_index1' c n t) (index_lift n' n 1) t' == bind_index1' (bind_index1' c n' t') (index_lift n n' 1) t) =
//   admit ()

// let bind_index_commute (c: context) (n: index { n <= List.length c.bound }) (t t': Type): Lemma (bind_index1' (bind_index1 c t) (n + 1) t' == bind_index1 (bind_index1' c n t') t) =
//   bind_index_commute c 0 n t t'
