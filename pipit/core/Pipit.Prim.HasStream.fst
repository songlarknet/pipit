(* Typeclass for lifting an F* [eqtype] into a [Pipit.Prim.Shallow.shallow_type].

  An instance of [has_stream a] gives Pipit:
    * [ty_id]: a unique-per-type identifier (used by CSE and by the variable
      equality axiom in [Pipit.Prim.Shallow]).
    * [val_default]: a designated default value of type [a]. This is *not* just
      metadata: it is the seed value used by [rec'] fixpoints in the executable
      transition system ([Pipit.System.Exec.Exp]), is referenced by the
      causality proof ([Pipit.Exp.Causality]), and acts as the abstract value
      of free variables in [Pipit.Abstract.System.Exp].

  [shallow] packages a [has_stream] instance into the [shallow_type] record
  consumed by [Pipit.Prim.Shallow.table].
*)
module Pipit.Prim.HasStream

module Shallow = Pipit.Prim.Shallow
module L       = FStar.List.Tot

class has_stream (a: eqtype) = {
  ty_id:       Shallow.ident;
  val_default: a;
}

let shallow (a: eqtype) {| strm: has_stream a |} : Shallow.shallow_type = {
  ty_id       = strm.ty_id;
  ty_sem      = a;
  val_default = strm.val_default;
}

instance has_stream_bool: has_stream bool = {
  ty_id       = [`%Prims.bool];
  val_default = false;
}

instance has_stream_int: has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}

instance has_stream_unit: has_stream unit = {
  ty_id       = [`%Prims.unit];
  val_default = ();
}

instance has_stream_tup2 {| a: has_stream 'a |} {| b: has_stream 'b |}: has_stream ('a & 'b) = {
  ty_id       = L.("tuple2:" :: a.ty_id @ b.ty_id);
  val_default = (a.val_default, b.val_default);
}
