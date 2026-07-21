module Pipit.Base.Context.Named

module L = FStar.List.Tot

unfold
type context (a: Type) = list (string & a)

inline_for_extraction
let empty (#a: Type): context a = []

inline_for_extraction
let lookup (#a: Type) (c: context a) (x: string): option a = L.assoc x c

inline_for_extraction
let update (#a: Type) (c: context a) (x: string) (v: a): context a = (x, v) :: c
