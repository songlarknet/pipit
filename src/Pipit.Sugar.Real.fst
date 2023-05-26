(* Syntactic sugar for real-valued streams *)
module Pipit.Sugar.Real

open Pipit.Sugar

module R = FStar.Real

type real = R.real
type nonzero = d: R.real { d <> 0.0R }
type pos = d: R.real { R.(d >=. 0.0R) }

type bools = s bool
type reals = s real

let ( +. ) : reals -> reals -> reals =
  liftA2 R.((+.))

let ( -. ) : reals -> reals -> reals =
  liftA2 R.((-.))

let ( *. ) : reals -> reals -> reals =
  liftA2 R.(( *. ))

let ( /. ) : reals -> s nonzero -> reals =
  liftA2 R.(( /. ))

let ( >.  ) : reals -> reals -> bools =
  liftA2 R.(( >. ))

let ( >=. ) : reals -> reals -> bools =
  liftA2 R.(( >=. ))

let ( <.  ) : reals -> reals -> bools =
  liftA2 R.(( <. ))
let ( <=. ) : reals -> reals -> bools =
  liftA2 R.(( <=. ))

let abs (r: reals) =
  let' r (fun r' ->
    if_then_else (r' >=. pure 0.0R) r' (pure 0.0R -. r'))
