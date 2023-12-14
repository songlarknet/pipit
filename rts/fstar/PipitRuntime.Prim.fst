(* Primitives
  These are not inlined by the tactics / normalizer settings.
  We set some of them to be inlined by krml for extracting C code, but
  the short-circuiting boolean primitives (&&) (||) etc can cause problems,
  so we don't inline them.
*)
module PipitRuntime.Prim

(* Delay normalisation on applications of this *)
inline_for_extraction
let p'delay (#a: Type) (x: a): a = x

let p'let (#a #b: Type) (x: a) (f: a -> b): b = f x

inline_for_extraction
let p'b'not (x: bool): bool = not x

let p'b'and (x y: bool): bool =
  x && y

let p'b'or (x y: bool): bool =
  x || y

let p'b'implies (x y: bool): bool =
  not x || y

inline_for_extraction
let p'select (#a: Type) (cond: bool) (t f: a): a =
  if cond then t else f
