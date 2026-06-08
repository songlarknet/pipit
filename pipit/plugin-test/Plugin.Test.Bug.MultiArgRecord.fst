(* TODO: README workaround 12 ("Lifter Error 19 on multi-arg stream
   functions returning a record").

   `Network.TTCan.Impl.Controller`'s `controller'` (13 stream args
   returning `stream controller_result`) and `controller` (10 stream
   args, same return) both fail the lifter with

     Error 19 at Pipit.Source.Ast.Lower.fst(...):
       - Subtyping check failed
       - Expected type Pipit.Context.Base.index_lookup __ctx_<id>_N
         got type Prims.int

   The failure persists with a minimal body (e.g. `PSSB.val_default`),
   so the issue is in the cexp-context construction for a function
   with many stream binders + a record return type, not in the body.

   This file pins the boundary:
     - `eg_few_args` (baseline) — small N stream args, record return:
       lifts cleanly.
     - `eg_many_args_min_body` (commented out) — large N stream args,
       record return, `PSSB.val_default` body: reproduces Error 19.

   Uncomment to reproduce. When fixed, remove the comment-out and drop
   workaround 12 from `example/ttcan2/README.md`. *)
module Plugin.Test.Bug.MultiArgRecord
#lang-pipit

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

#set-options "--warn_error -242"

(* Mimic `Clocked.t`: a polymorphic option-of-eqtype with a
   `has_stream` instance derived through a typeclass parameter. *)
type clk (a: eqtype) = option a

instance has_stream_clk (a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (clk a) = {
  ty_id       = `%clk :: (PSSB.ty_id #a);
  val_default = None;
}

(* Nested record (mimics `ref_message` carried inside `Clocked.t`). *)
type inner = {
  i_x: int;
  i_y: int;
}

instance has_stream_inner: PSSB.has_stream inner = {
  ty_id       = [`%inner];
  val_default = { i_x = 0; i_y = 0; };
}

(* Outer record with nested records inside option fields (mimics
   `controller_result` carrying `Clocked.t ref_message` etc.). *)
type result = {
  r_a: int;
  r_b: clk inner;
  r_c: clk bool;
  r_d: clk int;
  r_e: int;
}

instance has_stream_result: PSSB.has_stream result = {
  ty_id       = [`%result];
  val_default = { r_a = 0; r_b = None; r_c = None; r_d = None; r_e = 0; };
}

(* Static "config" prefix arg, also matching `controller'`. *)
type config = { cfg_n: int; }

(* Baseline: small number of stream args returning the record. *)
let eg_few_args
  (cfg: config)
  (a: stream int)
  (b: stream (clk inner))
  (c: stream (clk bool))
    : stream result =
  PSSB.val_default

(* Failing case: large number of stream args (mirrors `controller'`'s
   13 stream args + Static `cfg`), same record return type. The body
   constructs the result record by referencing several of the stream
   args. Reproduces

     Error 19 at Pipit.Source.Ast.Lower.fst(282,3-282,31):
       - Subtyping check failed
       - Expected type Pipit.Context.Base.index_lookup
                       __ctx_eg_many_args_min_body_19
         got type Prims.int

   identical (up to source/binder name) to the failure seen on
   `Network.TTCan.Impl.Controller.{controller', controller}`. Note
   that `PSSB.val_default` as the body does NOT reproduce it — the
   trigger seems to require an actual context-using body together
   with the many-stream-binder shape.

   Commented out so the rest of the module compiles. *)
//
// let eg_many_args_min_body
//   (cfg: config)
//   (a1:  stream int)
//   (a2:  stream (clk inner))
//   (a3:  stream (clk int))
//   (a4:  stream (clk bool))
//   (a5:  stream int)
//   (a6:  stream (clk int))
//   (a7:  stream (clk bool))
//   (a8:  stream int)
//   (a9:  stream (clk inner))
//   (a10: stream (clk bool))
//   (a11: stream int)
//   (a12: stream (clk int))
//   (a13: stream (clk bool))
//     : stream result =
//   { r_a = a1; r_b = a2; r_c = a4; r_d = a3; r_e = a5; }
