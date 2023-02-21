(* Dealing with value contexts (rows) and streaming contexts (tables) *)
module Pipit.Context.Base

module LT = FStar.List.Tot
module LTP = FStar.List.Tot.Properties

type value = bool

type vector (a: Type) (len: nat) = v: list a { List.length v == len }

(* A row is a vector of values *)
type row (inner: nat) =
 | Row: vector value inner -> row inner

(* A table is a vector of rows *)
type table (outer inner: nat) =
 | Table: vector (row inner) outer -> table outer inner

let rec vector_map (#n: nat) (#a #b: Type) (f: a -> b)
  (va: vector a n)
  : vector b n =
  match va with
  | [] -> []
  | aa :: va -> f aa :: vector_map #(n - 1) f va

let rec vector_map2 (#n: nat) (#a #b #c: Type) (f: a -> b -> c)
 (va: vector a n) (vb: vector b n)
  : vector c n =
 match va, vb with
 | [], [] -> []
 | aa :: va, bb :: vb -> f aa bb :: vector_map2 #(n - 1) f va vb

let vector_append (#n1 #n2: nat) (#a: Type)
  (va: vector a n1) (vb: vector a n2)
   : vector a (n1 + n2) =
   LTP.append_length va vb;
   LT.append va vb

let vector_hd (#n: nat) (#a: Type)
    (va: vector a (n + 1)): a = LT.hd va

let vector_tl (#n: nat) (#a: Type)
    (va: vector a (n + 1)): vector a n = LT.tl va

let row_append (#inner1 #inner2: nat) (r1: row inner1) (r2: row inner2)
  : row (inner1 + inner2) =
  let Row vs1 = r1 in
  let Row vs2 = r2 in
  Row (vector_append vs1 vs2)

(* Table append *)
let table_append (#outer1 #outer2 #inner: nat) (t1: table outer1 inner) (t2: table outer2 inner)
  : table (outer1 + outer2) inner =
 let Table rs1 = t1 in
 let Table rs2 = t2 in
 Table (vector_append rs1 rs2)

unfold
let (++) (#outer1 #outer2 #inner: nat) (t1: table outer1 inner) (t2: table outer2 inner) =
  table_append #outer1 #outer2 #inner t1 t2

(* Table lifted append *)
let table_map_append (#outer #inner1 #inner2: nat) (t1: table outer inner1) (t2: table outer inner2)
  : table outer (inner1 + inner2) =
  let Table rs1 = t1 in
  let Table rs2 = t2 in
  Table (vector_map2 row_append rs1 rs2)

unfold
let (++^) (#outer #inner1 #inner2: nat) (t1: table outer inner1) (t2: table outer inner2) =
  table_map_append #outer #inner1 #inner2 t1 t2

let vector1 (#a: Type) (v: a) : vector a 1 = [v]
let row1 (v: value) : row 1 = Row [v]
let table1 (#inner: nat) (r: row inner) : table 1 inner = Table [r]
let table_of_values (#outer: nat) (v: vector value outer) : table outer 1 = Table (vector_map row1 v)

let row_index (#inner: nat) (r: row inner) (ix: nat { ix < inner }) : value =
  let Row vs = r in
  LT.index vs ix

let table_index (#outer #inner: nat) (t: table outer inner) (ix: nat { ix < inner })
  : vector value outer =
  let Table rs = t in
  vector_map (fun r -> row_index r ix) rs

let table_const (#outer #inner: nat) (t: table outer inner) (v: value)
 : vector value outer =
  let Table rs = t in
  vector_map (fun _ -> v) rs

let table_hd (#outer #inner: nat) (t: table (outer + 1) inner): row inner =
  let Table (r :: _) = t in
  r

let table_tl (#outer #inner: nat) (t: table (outer + 1) inner): table outer inner =
  let Table (_ :: rs) = t in
  Table rs

let rec vector_take_snoc' (#len1 #len2: nat) (#a: Type) (t1: vector a len1) (mid: a) (t2: vector a len2):
    Tot (t': vector a (len1 + len2) & r': a { vector_append #len1 #(len2 + 1) t1 (mid :: t2) == vector_append t' (vector1 r') }) (decreases t2) =
 match t2 with
 | [] -> (| t1, mid |)
 | (r' :: rs') ->
   let (| t', r'' |) = vector_take_snoc' #(len1 + 1) #(len2 - 1) (vector_append t1 [mid]) r' rs' in
   LTP.append_assoc t1 [mid] t2;
   (| t', r'' |)

let vector_take_snoc (#len: nat) (#a: Type) (vs: vector a len):
    opt: option (_: unit { len > 0} & vs': vector a (len - 1) & r': a { vs == vector_append vs' (vector1 r') }) { None? opt ==> len = 0 } =
  match vs with
  | [] -> None
  | (v0 :: vs) ->
    let (| t', r' |) = vector_take_snoc' #0 #(len - 1) [] v0 vs in
    Some (| (), t', r' |)


let table_take_snoc (#outer #inner: nat) (t: table outer inner):
    opt: option (_: unit { outer > 0} & t': table (outer - 1) inner & r': row inner { t == table_append t' (table1 r') }) { None? opt ==> outer = 0 } =
  match t with
  | Table [] -> None
  | Table (v0 :: vs) ->
    let (| t', r' |) = vector_take_snoc' #0 #(outer - 1) [] v0 vs in
    Some (| (), Table t', r' |)

let vector_init (#len: nat) (#a: Type) (vs: vector a (len + 1)):
    vs': vector a len =
  let Some (| (), vs', _ |) = vector_take_snoc vs in
  vs'

let table_init (#outer: nat) (#inner: nat) (t: table (outer + 1) inner):
    t': table outer inner =
  let Some (| (), t', _ |) = table_take_snoc t in
  t'
