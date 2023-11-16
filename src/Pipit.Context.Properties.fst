(* Contexts and rows: contexts are lists of types; rows are instances of those
   types. This module has definitions for binding variables and lemmas about
   them. *)
module Pipit.Context.Properties

module List = FStar.List.Tot
module C = Pipit.Context.Base
module R = Pipit.Context.Row

(* Properties should only require one implicit unrolling of recursive definitions, and one implicit inversion *)
#push-options "--fuel 1 --ifuel 1"

let lemma_drop0 (c: C.context 'a { List.length c > 0 }):
  Lemma (ensures (C.drop1 c 0 == List.tl c)) = ()

let lemma_lift0 (c: C.context 'a) (t: 'a):
  Lemma (ensures (C.lift1 c 0 t == t :: c)) = ()

// XXX: these look like good candidates for SMT patterns but seem to cause flakiness
let lemma_dropCons (c0: 'a) (c': C.context 'a) (i: C.index { 0 < i /\ i <= List.length c' }):
  Lemma (ensures (C.drop1 (c0 :: c') i == c0 :: C.drop1 c' (i - 1)))
        = // [SMTPat (drop1 (c0 :: c') i)] =
  ()

let lemma_liftCons (c0: 'a) (c': C.context 'a) (i: C.index { 0 < i /\ i <= List.length c' + 1}) (t: 'a):
  Lemma (ensures (C.lift1 (c0 :: c') i t == c0 :: C.lift1 c' (i - 1) t))
        = // [SMTPat (lift1 (c0 :: c') i t)] =
  ()

let lemma_get_index_Cons (c0: 'a) (c': C.context 'a) (i1: C.index_lookup c'):
  Lemma (ensures (C.get_index (c0 :: c') (i1 + 1) == C.get_index c' i1)) = ()

let rec lemma_open_preserves_opt_index (c: C.context 'a) (n: C.index_lookup c) (i: C.index { i <> n }): Lemma (C.opt_index c i == C.opt_index (C.open1' c n) (C.index_drop i n)) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0 && i > 0
    then lemma_open_preserves_opt_index c' (n - 1) (i - 1)
    else ()

let rec lemma_close_preserves_opt_index (c: C.context 'a) (t: 'a) (n: C.index_insert c) (i: C.index): Lemma (C.opt_index c i == C.opt_index (C.close1' c t n) (C.index_lift i n)) =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0 && i > 0
    then lemma_close_preserves_opt_index c' t (n - 1) (i - 1)
    else ()

let rec lemma_close_contains (c: C.context 'a) (t: 'a) (n: C.index_insert c): Lemma (C.opt_index (C.close1' c t n) n == Some t)
  [SMTPat (C.opt_index (C.close1' c t n) n)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if n > 0
    then lemma_close_contains c' t (n - 1)
    else ()

let rec lemma_append_preserves_opt_index (c c': C.context 'a) (n: C.index_lookup c): Lemma (C.opt_index c n == C.opt_index (C.append c c') n) =
  match c with
  | [] -> ()
  | _ :: c1' ->
    if n > 0
    then lemma_append_preserves_opt_index c1' c' (n - 1)
    else ()


let rec lemma_append_preserves_get_index (c c': C.context 'a) (n: C.index_lookup c): Lemma (n < List.length (C.append c c') /\ C.get_index c n == C.get_index (C.append c c') n) =
  match c with
  | [] -> ()
  | _ :: c1' ->
    List.append_length c c';
    if n > 0
    then (lemma_append_preserves_get_index c1' c' (n - 1))
    else ()

let rec lemma_lift_lift_commute (c: C.context 'a) (i1: C.index_insert c) (i2: C.index { i2 <= i1 }) (t1 t2: 'a):
  Lemma (ensures C.lift1 (C.lift1 c i1 t1) i2 t2 == C.lift1 (C.lift1 c i2 t2) (i1 + 1) t1) =
  match c with
  | [] -> ()
  | c0 :: c' ->
    if i2 > 0
    then (lemma_lift_lift_commute c' (i1 - 1) (i2 - 1) t1 t2;
      ())
    else ()


let rec lemma_drop_drop_commute (c: C.context 'a) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.length c - 1 }):
  Lemma (ensures C.drop1 (C.drop1 c i1) i2 == C.drop1 (C.drop1 c (i2 + 1)) i1) =
  match c with
  | [] -> ()
  | c0 :: c' ->
    if i1 > 0
    then (lemma_drop_drop_commute c' (i1 - 1) (i2 - 1);
         ())

    else ()

let rec lemma_drop_lift_eq (c: C.context 'a) (i: C.index_insert c) (t: 'a):
  Lemma (ensures C.drop1 (C.lift1 c i t) i == c)
    [SMTPat (C.drop1 (C.lift1 c i t) i)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i > 0
    then lemma_drop_lift_eq c' (i - 1) t
    else ()

let rec lemma_lift_drop_eq (c: C.context 'a) (i: C.index_lookup c):
  Lemma (ensures C.lift1 (C.drop1 c i) i (C.get_index c i) == c)
    [SMTPat (C.lift1 (C.drop1 c i) i (C.get_index c i)) ]=
  match c with
  | [] -> ()
  | _ :: c' ->
    if i > 0
    then lemma_lift_drop_eq c' (i - 1)
    else ()

let rec lemma_lift_drop_commute_le (c: C.context 'a) (i1: C.index_lookup c) (i2: C.index { i2 <= i1 }) (t: 'a):
  Lemma (ensures (C.lift1 (C.drop1 c i1) i2 t == C.drop1 (C.lift1 c i2 t) (i1 + 1))) =
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

let rec lemma_lift_get_index (c: C.context 'a) (i1: C.index_insert c) (i2: C.index_insert c) (t2: 'a):
  Lemma (ensures C.get_index (C.lift1 c i2 t2) i1 == (if i1 = i2 then t2 else C.get_index c (C.index_drop i1 i2)))
        [SMTPat (C.get_index (C.lift1 c i2 t2) i1)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i1 > 0 && i2 > 0
    then
      lemma_lift_get_index c' (i1 - 1) (i2 - 1) t2
    else ()

let lemma_lift_get_index_eq (c: C.context 'a) (i: C.index_insert c) (t: 'a):
  Lemma (ensures C.get_index (C.lift1 c i t) i == t)
        [SMTPat (C.get_index (C.lift1 c i t) i)] =
  lemma_lift_get_index c i i t

let lemma_lift_get_index_gt (c: C.context 'a) (i1: C.index_lookup c) (i2: C.index { i2 <= i1 }) (t2: 'a):
  Lemma (ensures C.get_index (C.lift1 c i2 t2) (i1 + 1) == C.get_index c i1) =
  lemma_lift_get_index c (i1 + 1) i2 t2

// let lemma_lift_get_index_gt (c: context) (i1: index { i1 <= List.length c }) (i2: index { i2 <= i1 /\ i2 <= List.length c }) (t2: Type):
//   Lemma (ensures get_index (lift1 c i2 t2) i1 == get_index c (i1 - 1)) =
//   lemma_lift_get_index c i1 i2 t2

let rec lemma_drop_get_index (c: C.context 'a) (i1: C.index_lookup c) (i2: C.index { i2 < List.length c - 1 }):
  Lemma (ensures C.get_index (C.drop1 c i1) i2 == C.get_index c (C.index_lift i2 i1))
        [SMTPat (C.get_index (C.drop1 c i1) i2)] =
  match c with
  | [] -> ()
  | _ :: c' ->
    if i1 > 0 && i2 > 0
    then
      lemma_drop_get_index c' (i1 - 1) (i2 - 1)
    else ()

let lemma_drop_get_index_gt (c: C.context 'a) (i1: C.index_lookup c) (i2: C.index { i1 <= i2 /\ i2 < List.length c - 1 }):
  Lemma (ensures C.get_index (C.drop1 c i1) i2 == C.get_index c (i2 + 1)) =
  lemma_drop_get_index c i1 i2

let lemma_drop_get_index_lt (c: C.context 'a) (i1: C.index_lookup c) (i2: C.index { i2 < i1 /\ i2 < List.length c - 1 }):
  Lemma (ensures C.get_index (C.drop1 c i1) i2 == C.get_index c i2) =
  lemma_drop_get_index c i1 i2

let row_lift1_dropped (i: C.index_lookup 'c) (r: R.row (C.drop1 'c i)) (v: C.get_index 'c i): R.row 'c =
  lemma_lift_drop_eq 'c i;
  R.lift1 r i v

let row_zip2_lift1_dropped (i: C.index_lookup 'c) (rs: list (R.row (C.drop1 'c i))) (vs: list (C.get_index 'c i) { List.length rs == List.length vs }): (ret: list (R.row 'c) { List.length ret == List.length rs }) =
  lemma_lift_drop_eq 'c i;
  R.zip2_lift1 rs i vs

let rec lemma_row_index_lift1_eq
  (#a: eqtype)
  (r: R.row 'c)
  (i: C.index_insert 'c)
  (v: a):
  Lemma (ensures (R.index (C.lift1 'c i a) (R.lift1 r i v) i == v))
        [SMTPat (R.index (C.lift1 'c i a) (R.lift1 r i v) i)] =
  match 'c with
   | [] -> ()
   | c :: c' ->
     let r': c & R.row c' = r in
     if i = 0
     then ()
     else lemma_row_index_lift1_eq (snd r') (i - 1) v

let rec lemma_row_index_lift1
  (#a: eqtype)
  (r: R.row 'c)
  (i: C.index_insert 'c)
  (i': C.index_insert 'c)
  (v: a):
  Lemma (ensures (R.index (C.lift1 'c i a) (R.lift1 r i v) i' == (if i = i' then v else (coerce_eq () (R.index 'c r (C.index_drop i' i))))))
        [SMTPat (R.index (C.lift1 'c i a) (R.lift1 r i v) i')] =
  match 'c with
   | [] -> ()
   | c :: c' ->
     let r': c & R.row c' = r in
     if i = 0 || i' = 0
     then ()
     else lemma_row_index_lift1 (snd r') (i - 1) (i' - 1) v

let rec lemma_row_zip2_lift1_row_zip2_cons
  (#a: eqtype)
  (rows: list (R.row 'c))
  (vs: list a { List.length rows == List.length vs }):
  Lemma (ensures (R.zip2_lift1 rows 0 vs == R.zip2_cons vs rows))
        [SMTPat (R.zip2_lift1 rows 0 vs)] =
  match rows, vs with
  | [], [] -> ()
  | _ :: rows', _ :: vs' ->
    lemma_row_zip2_lift1_row_zip2_cons rows' vs'
