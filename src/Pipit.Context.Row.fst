(* Rows: contexts are lists of types, and rows are instances of contexts. *)
module Pipit.Context.Row

module C = Pipit.Context.Base

let rec row (l: C.context_t): Type =
  match l with
  | [] -> unit
  | t :: ts -> t * row ts

let rec index (l: C.context_t) (r: row l) (i: C.index_lookup l): C.get_index l i =
  match l with
  | t :: ts ->
    let r': t * row (List.tl l) = r in
    match r' with
    | (r0, rs) ->
      if i = 0
      then r0
      else (
        // Why coerce required?
        let res: List.index ts (i - 1) = index ts rs (i - 1) in
        coerce_eq #_ #(List.index l i) () res)

let rec row_append (r: row 'c) (r': row 'd): row (List.append 'c 'd) =
  match 'c with
  | [] -> r'
  | t :: ts ->
    let rr: (t & row ts) = r in
    let (rt, rts) = rr in
    (rt, row_append rts r')

let row_cons (a: 'a) (r: row 'c): row ('a :: 'c) = (a, r)

let rec row_lift1 (r: row 'c) (i: nat { i <= List.length 'c }) (v: 'a): row (lift1 'c i 'a) =
  if i = 0 then (v, r)
  else
    match 'c with
    | t :: ts ->
      let rr: (t & row ts) = r in
      let (rt, rts) = rr in
      (rt, row_lift1 rts (i - 1) v)

let rec row_zip2_append (rs: list (row 'c)) (rs': list (row 'd) { List.length rs == List.length rs' }): list (row (List.append 'c 'd)) =
  match rs, rs' with
  | [], [] -> []
  | r :: rs, r' :: rs' -> (row_append r r') :: row_zip2_append rs rs'

let rec row_zip2_cons (rs: list 'a) (rs': list (row 'd) { List.length rs == List.length rs' }): (ret: list (row ('a :: 'd)) { List.length ret == List.length rs }) =
  match rs, rs' with
  | [], [] -> []
  | r :: rs, r' :: rs' -> (row_cons r r') :: row_zip2_cons rs rs'

let rec row_zip2_lift1 (rs: list (row 'c)) (i: nat { i <= List.length 'c }) (vs: list 'a { List.length rs == List.length vs }): (ret: list (row (lift1 'c i 'a)) { List.length ret == List.length rs }) =
  match rs, vs with
  | [], [] -> []
  | r :: rs, v :: vs -> row_lift1 r i v :: row_zip2_lift1 rs i vs
