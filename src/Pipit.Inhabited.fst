(* Default or bottom: some interpretations of recursive expressions need an
   initial value just to seed the computation, even though the value will
   never be inspected. *)
module Pipit.Inhabited

class inhabited (a: Type) = {
  get_inhabited: a
}

instance inhabited_int: inhabited int = {
  get_inhabited = 0;
}

instance inhabited_bool: inhabited bool = {
  get_inhabited = false;
}
