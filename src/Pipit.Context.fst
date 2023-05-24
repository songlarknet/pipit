module Pipit.Context

module Map = FStar.FiniteMap.Base
module List = FStar.List.Tot


type var (t: Type) =
  (* Keep constructor so "var int" is different from "var string" *)
  | Var: (v: nat) -> var t
let index  = nat

(* AXIOM: we trust that all fresh name allocation doesn't reuse names!
   We can't use decidable equality on two variables of different type variables
   (x: var 'a) and (x': var 'b) because equality on Type isn't decidable.
 *)
let axiom_variables_require_fresh_indices (x: var 'a) (x': var 'b { Var?.v x = Var?.v x' }): Lemma ('a == 'b) = admit ()

let var_eq (x: var 'a) (x': var 'b):
  (eq: bool { eq <==> x === x' }) =
  if Var?.v x = Var?.v x'
  then (axiom_variables_require_fresh_indices x x'; true)
  else false


type context = list Type

let has_index (c: context) (i: index) = i < List.length c
let get_index (c: context) (i: index { has_index c i }): Type = List.index c i
let opt_index (c: context) (i: index): option Type = if has_index c i then Some (get_index c i) else None

let empty = []

let append (c c': context): context = List.append c c'

let rec drop1 (l: list 'a) (i: nat { i < List.length l }): (l': list 'a { List.length l' == List.length l - 1 }) =
  match l, i with
  | _ :: l', 0 -> l'
  | l0 :: l', _ -> l0 :: drop1 l' (i - 1)

let rec lift1 (l: list 'a) (i: nat { i <= List.length l }) (v: 'a): (l': list 'a { List.length l' == List.length l + 1 }) =
  match l, i with
  | _, 0 -> v :: l
  | l0 :: l', _ -> l0 :: lift1 l' (i - 1) v

let rec row (l: context): Type =
  match l with
  | [] -> unit
  | t :: ts -> t * row ts

let rec row_index (l: context) (r: row l) (i: index { i < List.length l }): get_index l i =
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

let index_drop (i limit: index): (r: index { (i > limit ==> r = i - 1) /\ (i <= limit ==> r = i )}) =
  if i > limit then i - 1 else i

let index_lift (i limit: index): (r: index { (i >= limit ==> r = i + 1) /\ (i < limit ==> r = i) }) =
  if i >= limit then i + 1 else i

let open1' (c: context) (i: index { has_index c i }): context = drop1 c i
let open1 (c: context { has_index c 0 }): context = List.tl c

let close1' (c: context) (t: Type) (i: index { i <= List.length c }): context = lift1 c i t
let close1 (c: context) (t: Type): context = t :: c

(* Properties should only require one implicit unrolling of recursive definitions, and one implicit inversion *)
#push-options "--fuel 1 --ifuel 1"

let lemma_drop0 (c: context { List.length c > 0 }):
  Lemma (ensures (drop1 c 0 == List.tl c)) = ()

let lemma_lift0 (c: context) (t: Type):
  Lemma (ensures (lift1 c 0 t == t :: c)) = ()

// XXX: these look like good candidates for SMT patterns but seem to cause flakiness
let lemma_dropCons (c0: Type) (c': context) (i: index { 0 < i /\ i <= List.length c' }):
  Lemma (ensures (drop1 (c0 :: c') i == c0 :: drop1 c' (i - 1)))
        = // [SMTPat (drop1 (c0 :: c') i)] =
  ()

let lemma_liftCons (c0: Type) (c': context) (i: index { 0 < i /\ i <= List.length c' + 1}) (t: Type):
  Lemma (ensures (lift1 (c0 :: c') i t == c0 :: lift1 c' (i - 1) t))
        = // [SMTPat (lift1 (c0 :: c') i t)] =
  ()

let rec lemma_open_preserves_opt_index (c: context) (n: index { has_index c n }) (i: index { i <> n }): Lemma (opt_index c i == opt_index (open1' c n) (index_drop i n)) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0 && i > 0
    then lemma_open_preserves_opt_index c' (n - 1) (i - 1)
    else ()

let rec lemma_close_preserves_opt_index (c: context) (t: Type) (n: index { n <= List.length c }) (i: index): Lemma (opt_index c i == opt_index (close1' c t n) (index_lift i n)) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0 && i > 0
    then lemma_close_preserves_opt_index c' t (n - 1) (i - 1)
    else ()

let rec lemma_close_contains (c: context) (t: Type) (n: index { n <= List.length c }): Lemma (opt_index (close1' c t n) n == Some t)
  [SMTPat (opt_index (close1' c t n) n)] =
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

let rec lemma_lift_lift_commute (c: context) (i1: index { i1 <= List.length c }) (i2: index { i2 <= i1 }) (t1 t2: Type):
  Lemma (ensures lift1 (lift1 c i1 t1) i2 t2 == lift1 (lift1 c i2 t2) (i1 + 1) t1) =
  match c with
  | [] -> ()
  | c0 :: c' ->
    if i2 > 0
    then (lemma_lift_lift_commute c' (i1 - 1) (i2 - 1) t1 t2;
      ())
    else ()


let rec lemma_drop_drop_commute (c: context) (i1: index { has_index c i1 }) (i2: index { i1 <= i2 /\ i2 < List.length c - 1 }):
  Lemma (ensures drop1 (drop1 c i1) i2 == drop1 (drop1 c (i2 + 1)) i1) =
  match c with
  | [] -> ()
  | c0 :: c' ->
    if i1 > 0
    then (lemma_drop_drop_commute c' (i1 - 1) (i2 - 1);
         ())

    else ()

let rec lemma_drop_lift_eq (c: context) (i: index { i <= List.length c }) (t: Type):
  Lemma (ensures drop1 (lift1 c i t) i == c)
    [SMTPat (drop1 (lift1 c i t) i)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i > 0
    then lemma_drop_lift_eq c' (i - 1) t
    else ()

let rec lemma_lift_drop_eq (c: context) (i: index { i < List.length c }):
  Lemma (ensures lift1 (drop1 c i) i (get_index c i) == c)
    [SMTPat (lift1 (drop1 c i) i (get_index c i)) ]=
  match c with
  | [] -> ()
  | _ :: c' ->
    if i > 0
    then lemma_lift_drop_eq c' (i - 1)
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

let rec lemma_lift_get_index (c: context) (i1: index { i1 <= List.length c }) (i2: index { i2 <= List.length c }) (t2: Type):
  Lemma (ensures get_index (lift1 c i2 t2) i1 == (if i1 = i2 then t2 else get_index c (index_drop i1 i2)))
        [SMTPat (get_index (lift1 c i2 t2) i1)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i1 > 0 && i2 > 0
    then
      lemma_lift_get_index c' (i1 - 1) (i2 - 1) t2
    else ()

let lemma_lift_get_index_eq (c: context) (i: index { i <= List.length c }) (t: Type):
  Lemma (ensures get_index (lift1 c i t) i == t)
        [SMTPat (get_index (lift1 c i t) i)] =
  lemma_lift_get_index c i i t

let lemma_lift_get_index_gt (c: context) (i1: index { has_index c i1 }) (i2: index { i2 <= i1 }) (t2: Type):
  Lemma (ensures get_index (lift1 c i2 t2) (i1 + 1) == get_index c i1) =
  lemma_lift_get_index c (i1 + 1) i2 t2

// let lemma_lift_get_index_gt (c: context) (i1: index { i1 <= List.length c }) (i2: index { i2 <= i1 /\ i2 <= List.length c }) (t2: Type):
//   Lemma (ensures get_index (lift1 c i2 t2) i1 == get_index c (i1 - 1)) =
//   lemma_lift_get_index c i1 i2 t2

let rec lemma_drop_get_index (c: context) (i1: index { has_index c i1 }) (i2: index { i2 < List.length c - 1 }):
  Lemma (ensures get_index (drop1 c i1) i2 == get_index c (index_lift i2 i1))
        [SMTPat (get_index (drop1 c i1) i2)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i1 > 0 && i2 > 0
    then
      lemma_drop_get_index c' (i1 - 1) (i2 - 1)
    else ()

let lemma_drop_get_index_gt (c: context) (i1: index { has_index c i1 }) (i2: index { i1 <= i2 /\ i2 < List.length c - 1 }):
  Lemma (ensures get_index (drop1 c i1) i2 == get_index c (i2 + 1)) =
  lemma_drop_get_index c i1 i2

let lemma_drop_get_index_lt (c: context) (i1: index { has_index c i1 }) (i2: index { i2 < i1 /\ i2 < List.length c - 1 }):
  Lemma (ensures get_index (drop1 c i1) i2 == get_index c i2) =
  lemma_drop_get_index c i1 i2

let row_lift1_dropped (i: nat { i < List.length 'c }) (r: row (drop1 'c i)) (v: get_index 'c i): row 'c =
  lemma_lift_drop_eq 'c i;
  row_lift1 r i v

let row_zip2_lift1_dropped (i: nat { i < List.length 'c }) (rs: list (row (drop1 'c i))) (vs: list (get_index 'c i) { List.length rs == List.length vs }): (ret: list (row 'c) { List.length ret == List.length rs }) =
  lemma_lift_drop_eq 'c i;
  row_zip2_lift1 rs i vs

let rec lemma_row_index_lift1_eq
  (r: row 'c)
  (i: index { i <= List.length 'c })
  (v: 'a):
  Lemma (ensures (row_index (lift1 'c i 'a) (row_lift1 r i v) i == v))
        [SMTPat (row_index (lift1 'c i 'a) (row_lift1 r i v) i)] =
  match 'c with
   | [] -> ()
   | c :: c' ->
     let r': c & row c' = r in
     if i = 0
     then ()
     else lemma_row_index_lift1_eq (snd r') (i - 1) v

let rec lemma_row_index_lift1
  (r: row 'c)
  (i: index { i <= List.length 'c })
  (i': index { i' <= List.length 'c })
  (v: 'a):
  Lemma (ensures (row_index (lift1 'c i 'a) (row_lift1 r i v) i' == (if i = i' then v else (coerce_eq () (row_index 'c r (index_drop i' i))))))
        [SMTPat (row_index (lift1 'c i 'a) (row_lift1 r i v) i')] =
  match 'c with
   | [] -> ()
   | c :: c' ->
     let r': c & row c' = r in
     if i = 0 || i' = 0
     then ()
     else lemma_row_index_lift1 (snd r') (i - 1) (i' - 1) v

let rec lemma_row_zip2_lift1_row_zip2_cons
  (rows: list (row 'c))
  (vs: list 'a { List.length rows == List.length vs }):
  Lemma (ensures (row_zip2_lift1 rows 0 vs == row_zip2_cons vs rows))
        [SMTPat (row_zip2_lift1 rows 0 vs)] =
  match rows, vs with
  | [], [] -> ()
  | _ :: rows', _ :: vs' ->
    lemma_row_zip2_lift1_row_zip2_cons rows' vs'
