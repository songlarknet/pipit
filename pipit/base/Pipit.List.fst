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

