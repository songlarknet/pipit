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
