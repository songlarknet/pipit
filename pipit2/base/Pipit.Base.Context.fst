module Pipit.Base.Context

module L = FStar.List.Tot

type context (a: Type) = list a

let index = nat

let has_index (c: context 'a) (i: index): bool = i < L.length c

let get_index (c: context 'a) (i: index { has_index c i }): 'a = L.index c i

let opt_index (c: context 'a) (i: index): option 'a =
  if has_index c i then Some (get_index c i) else None

let empty (#a: Type): context a = []

let close1 (c: context 'a) (t: 'a): context 'a = t :: c

let open1 (c: context 'a { has_index c 0 }): context 'a = L.tl c

let index_lift (i limit: index): index = if i >= limit then i + 1 else i

let index_drop (i limit: index): index = if i > limit then i - 1 else i

let index_lifts (i limit: index) (n: nat): index = if i >= limit then i + n else i
