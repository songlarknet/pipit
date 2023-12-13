module PipitRuntime.Prim

(* Delay normalisation on applications of this *)
inline_for_extraction
let p'delay (#a: Type) (x: a): a = x

let p'let (#a #b: Type) (x: a) (f: a -> b): b = f x

// TODO: try with tac_opaque to defer unfolding:
// [@"tac_opaque"]
inline_for_extraction
let p'b'not (x: bool): bool = not x

inline_for_extraction
let p'b'and (x y: bool): bool =
  x && y
  // if x then y else false

inline_for_extraction
let p'b'or (x y: bool): bool =
  x || y
  // if x then true else y

inline_for_extraction
let p'b'implies (x y: bool): bool =
  not x || y
  // if x then y else true

inline_for_extraction
let p'select (#a: Type) (cond: bool) (t f: a): a =
  if cond then t else f
