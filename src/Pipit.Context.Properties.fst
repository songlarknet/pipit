module Pipit.Context.Properties

open Pipit.Context.Base

module LT = FStar.List.Tot
module LTP = FStar.List.Tot.Properties

(* Properties *)
let rec vector_index_append1 (#inner1 #inner2: nat) (#a: Type)
  (v1: vector a inner1) (v2: vector a inner2) (ix: nat { ix < inner1 })
    : Lemma (ensures LT.index (vector_append v1 v2) ix == LT.index v1 ix) =
  match v1 with
  | [] -> ()
  | (vv :: v1') ->
    if ix = 0
    then ()
    else vector_index_append1 #(inner1 - 1) v1' v2 (ix - 1)

let rec vector_index_append2 (#inner1 #inner2: nat) (#a: Type)
  (v1: vector a inner1) (v2: vector a inner2) (ix: nat { inner1 <= ix /\ ix < inner1 + inner2 })
    : Lemma (ensures LT.index (vector_append v1 v2) ix == LT.index v2 (ix - inner1)) =
  match v1 with
  | [] -> ()
  | (vv :: v1') ->
    if ix = 0
    then ()
    else vector_index_append2 #(inner1 - 1) v1' v2 (ix - 1)


let row_index_row1 (v: value)
    : Lemma (ensures row_index (row1 v) 0 = v) =
  ()

let row_index_append1 (#inner1 #inner2: nat)
  (r1: row inner1) (r2: row inner2) (ix: nat { ix < inner1 })
    : Lemma (ensures row_index (row_append r1 r2) ix = row_index r1 ix) =
  let Row v1 = r1 in
  let Row v2 = r2 in
  vector_index_append1 v1 v2 ix

let row_index_append2 (#inner1 #inner2: nat)
  (r1: row inner1) (r2: row inner2) (ix: nat { inner1 <= ix /\ ix < inner1 + inner2 })
    : Lemma (ensures row_index (row_append r1 r2) ix = row_index r2 (ix - inner1)) =
  let Row v1 = r1 in
  let Row v2 = r2 in
  vector_index_append2 v1 v2 ix

let table_index_table1 (#inner: nat)
  (r1: row inner) (ix: nat { ix < inner })
    : Lemma (ensures table_index (table1 r1) ix = [row_index r1 ix]) =
  ()

let rec table_index_table_of_values (#outer: nat)
  (vs: vector value outer)
    : Lemma (ensures table_index (table_of_values vs) 0 = vs) =
  match vs with
  | [] -> ()
  | _ :: vs' ->
    table_index_table_of_values #(outer - 1) vs'

let rec table_index_append_outer (#outer1 #outer2 #inner: nat)
  (t1: table outer1 inner) (t2: table outer2 inner) (ix: nat { ix < inner })
    : Lemma (ensures table_index (t1 ++ t2) ix = vector_append (table_index t1 ix) (table_index t2 ix)) =
 match t1 with
 | Table [] -> ()
 | Table (r :: t1') ->
   table_index_append_outer (Table #(outer1 - 1) t1') t2 ix

let rec table_index_append_inner1 (#outer #inner1 #inner2: nat)
  (t1: table outer inner1) (t2: table outer inner2) (ix: nat { ix < inner1 })
    : Lemma (ensures table_index (t1 ++^ t2) ix = table_index t1 ix) =
  match t1, t2 with
  | Table [], Table [] -> ()
  | Table (r1 :: t1'), Table (r2 :: t2') ->
    row_index_append1 r1 r2 ix;
    table_index_append_inner1 (Table #(outer - 1) t1') (Table #(outer - 1) t2') ix

let rec table_index_append_inner2 (#outer #inner1 #inner2: nat)
  (t1: table outer inner1) (t2: table outer inner2) (ix: nat { inner1 <= ix /\ ix < inner1 + inner2 })
    : Lemma (ensures table_index (t1 ++^ t2) ix = table_index t2 (ix - inner1)) =
  match t1, t2 with
  | Table [], Table [] -> ()
  | Table (r1 :: t1'), Table (r2 :: t2') ->
    row_index_append2 r1 r2 ix;
    table_index_append_inner2 (Table #(outer - 1) t1') (Table #(outer - 1) t2') ix


let rec table_const_const (#outer #inner1 #inner2: nat)
  (t1: table outer inner1) (t2: table outer inner2) (v: value)
    : Lemma (ensures table_const t1 v = table_const t2 v) =
  match t1, t2 with
  | Table [], Table [] -> ()
  | Table (r :: t1'), Table (r' :: t2') ->
    table_const_const (Table #(outer - 1) t1') (Table #(outer - 1) t2') v

let rec table_const_append_outer (#outer1 #outer2 #inner: nat)
  (t1: table outer1 inner) (t2: table outer2 inner) (v: value)
    : Lemma (ensures table_const (t1 ++ t2) v = vector_append (table_const t1 v) (table_const t2 v)) =
  match t1 with
  | Table [] -> ()
  | Table (r :: t1') ->
    table_const_append_outer (Table #(outer1 - 1) t1') t2 v

let rec table_append_injective (#outer1 #outer2 #inner: nat)
  (t11 t12: table outer1 inner) (t21 t22: table outer2 inner):
    Lemma (requires table_append t11 t21 == table_append t12 t22)
          (ensures t11 == t12 /\ t21 == t22) =
  match t11, t12 with
  | Table [], Table [] -> ()
  | Table (x :: t11'), Table (y :: t12') ->
    table_append_injective (Table t11') (Table #(outer1 - 1) t12') t21 t22

