(* List helper lemmas *)
module Pipit.List

module L = FStar.List.Tot

let rec zip2 (#x #y: Type) (xs: list x) (ys: list y): list (x & y)
  = match xs, ys with
  | x::xs, y::ys -> (x,y) :: zip2 xs ys
  | _ -> []

let rec lemma_splitAt_length (i: nat) (l: list 'a):
  Lemma (ensures L.length (fst (L.splitAt i l)) + L.length (snd (L.splitAt i l)) = L.length l) =
  match i, l with
  | 0, _
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_length (i - 1) l'

(* Split a list at the first element that fails predicate `p`.
   Returns `(prefix, suffix)` where every element of `prefix` satisfies
   `p` and `suffix` is the rest (its head, if any, fails `p`). Like
   Haskell's `Data.List.span`. Differs from `L.splitAt` (index-based)
   and `L.partition` (re-orders by predicate). *)
let rec split_prefix (#a: Type) (p: a -> bool) (xs: list a): list a & list a =
  match xs with
  | [] -> ([], [])
  | x :: rest ->
    if p x then
      let (pre, suf) = split_prefix p rest in
      (x :: pre, suf)
    else
      ([], xs)

