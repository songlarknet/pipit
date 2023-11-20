module PipitRuntime.Prim.Bool

// TODO: try with tac_opaque to defer unfolding:
// [@"tac_opaque"]
let p'b'not (x: bool): bool = not x

let p'b'and (x y: bool): bool =
  if x then y else false

let p'b'or (x y: bool): bool =
  if x then true else y

let p'b'implies (x y: bool): bool =
  if x then y else true

let p'select (#a: Type) (cond: bool) (t f: a): a =
  if cond then t else f
