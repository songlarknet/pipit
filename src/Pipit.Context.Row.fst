(* Rows: contexts are lists of types, and rows are instances of contexts. *)
module Pipit.Context.Row

module List = FStar.List.Tot
module C = Pipit.Context.Base

let rec row (l: C.context Type): Type =
  match l with
  | [] -> unit
  | t :: ts -> t * row ts

let rec index (l: C.context Type) (r: row l) (i: C.index_lookup l): C.get_index l i =
  match l with
  | t :: ts ->
    let r': t * row (List.tl l) = r in
    match r' with
    | (r0, rs) ->
      if i = 0
      then r0
      else (
        // Why coerce required?
        let res: C.get_index ts (i - 1) = index ts rs (i - 1) in
        coerce_eq #_ #(List.index l i) () res)

let rec rev_acc (r: row 'c) (r': row 'd): row (C.rev_acc 'c 'd) =
  match 'c with
  | [] -> r'
  | t :: ts ->
    let rr: (t & row ts) = r in
    let (rt, rts) = rr in
    let r'': (row (t :: 'd)) = (rt, r') in
    rev_acc rts r''

let rec append (r: row 'c) (r': row 'd): row (C.append 'c 'd) =
  match 'c with
  | [] -> r'
  | t :: ts ->
    let rr: (t & row ts) = r in
    let (rt, rts) = rr in
    (rt, append rts r')

let cons (#a: Type) (v: a) (r: row 'c): row (a :: 'c) = (v, r)

let rec lift1 (#a: Type) (r: row 'c) (i: C.index_insert 'c) (v: a): row (C.lift1 'c i a) =
  if i = 0 then (v, r)
  else
    match 'c with
    | t :: ts ->
      let rr: (t & row ts) = r in
      let (rt, rts) = rr in
      (rt, lift1 rts (i - 1) v)

let rec zip2_append (rs: list (row 'c)) (rs': list (row 'd) { List.length rs == List.length rs' }): list (row (List.append 'c 'd)) =
  match rs, rs' with
  | [], [] -> []
  | r :: rs, r' :: rs' -> (append r r') :: zip2_append rs rs'

let rec zip2_cons (#a: Type) (rs: list a) (rs': list (row 'd) { List.length rs == List.length rs' }): (ret: list (row (a :: 'd)) { List.length ret == List.length rs }) =
  match rs, rs' with
  | [], [] -> []
  | r :: rs, r' :: rs' -> (cons r r') :: zip2_cons rs rs'

let rec zip2_lift1 (#a: Type) (rs: list (row 'c)) (i: C.index_insert 'c) (vs: list a { List.length rs == List.length vs }): (ret: list (row (C.lift1 'c i a)) { List.length ret == List.length rs }) =
  match rs, vs with
  | [], [] -> []
  | r :: rs, v :: vs -> lift1 r i v :: zip2_lift1 rs i vs
