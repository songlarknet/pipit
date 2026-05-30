(* Smoke test for `Pipit.Source.Ast.Lower`.

   Hand-builds small `Ast.ast` values and emits each via a splice-sigelt,
   mirroring how `Pipit.Plugin.Lift.core_sigelt` registers a lifted body
   with `lb_typ = Tv_Unknown` so F* infers its full type. *)
module Plugin.Test.Ast.Lower.Smoke

module T   = FStar.Tactics.V2
module R   = FStar.Range
module Ref = FStar.Reflection.V2

module Ast = Pipit.Source.Ast
module L   = Pipit.Source.Ast.Lower
module PPI = Pipit.Plugin.Interface
module PPS = Pipit.Prim.Shallow
module PXB = Pipit.Exp.Base
module PSSB = Pipit.Prim.HasStream

(* Build a top-level let-binding sigelt with an explicit expected type.
   We pin `lb_typ` (rather than leaving it `Tv_Unknown` as `core_sigelt`
   does) because the smoke-test bodies are small enough that there is no
   surrounding XApp/XLet structure to constrain XVal/XBVar implicits;
   the explicit type forces F* to refine them. *)
let mk_sigelt (nm: string) (ty: T.term) (tm: T.term) : T.Tac T.sigelt =
  let m       = T.cur_module () in
  let nm_full = List.Tot.append m [nm] in
  let lb: T.letbinding = {
    lb_fv  = T.pack_fv nm_full;
    lb_us  = [];
    lb_typ = ty;
    lb_def = tm;
  } in
  T.pack_sigelt (T.Sg_Let { isrec = false; lbs = [lb] })

(* ----- 1. literal -----
   `lower` of `ALit 0` in empty env should produce `XBase (XVal 0)`. *)

let _smoke_lit_sigelts () : T.Tac (list T.sigelt) =
  let int_ty: Ast.sty = `int in
  let lit: Ast.lit    = { Ast.lit_ty = int_ty; Ast.lit_tm = `(0 <: int) } in
  let a: Ast.ast      = Ast.ALit R.range_0 lit in
  let tm = L.lower L.empty_env a in
  [ mk_sigelt "smoke_lit" (`(PXB.exp PPS.table [] (PSSB.shallow int))) tm ]

%splice[smoke_lit] (_smoke_lit_sigelts ())

(* ----- 2. bound stream variable -----
   `lower` of `AVar "x" Stream` with `x: int` at de Bruijn index 0. *)

let _smoke_var_sigelts () : T.Tac (list T.sigelt) =
  let int_ty: Ast.sty = `int in
  let env: L.lower_env =
    { L.binders = [ ({ L.b_name = "x"; L.b_sty = int_ty; L.b_kind = L.BStream } <: L.binder) ];
      L.inst_for = (fun _ -> None) }
  in
  let a: Ast.ast = Ast.AVar R.range_0 "x" PPI.Stream in
  let tm = L.lower env a in
  [ mk_sigelt "smoke_var" (`(PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int))) tm ]

%splice[smoke_var] (_smoke_var_sigelts ())

(* ----- 3. fby with bound stream tail -----
   `lower` of `0 `fby` x` with `x: int` in context. *)

let _smoke_fby_sigelts () : T.Tac (list T.sigelt) =
  let int_ty: Ast.sty = `int in
  let lit:    Ast.lit = { Ast.lit_ty = int_ty; Ast.lit_tm = `(0 <: int) } in
  let env: L.lower_env =
    { L.binders = [ ({ L.b_name = "x"; L.b_sty = int_ty; L.b_kind = L.BStream } <: L.binder) ];
      L.inst_for = (fun _ -> None) }
  in
  let a: Ast.ast = Ast.AFby R.range_0 lit (Ast.AVar R.range_0 "x" PPI.Stream) in
  let tm = L.lower env a in
  [ mk_sigelt "smoke_fby" (`(PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int))) tm ]

%splice[smoke_fby] (_smoke_fby_sigelts ())

(* ----- 4. let stream -----
   `let y = (0 `fby` x) in y` with `x: int` in context. *)

let _smoke_let_stream_sigelts () : T.Tac (list T.sigelt) =
  let int_ty: Ast.sty = `int in
  let lit:    Ast.lit = { Ast.lit_ty = int_ty; Ast.lit_tm = `(0 <: int) } in
  let env: L.lower_env =
    { L.binders = [ ({ L.b_name = "x"; L.b_sty = int_ty; L.b_kind = L.BStream } <: L.binder) ];
      L.inst_for = (fun _ -> None) }
  in
  let def: Ast.ast =
    Ast.AFby R.range_0 lit (Ast.AVar R.range_0 "x" PPI.Stream)
  in
  let body: Ast.ast =
    Ast.AVar R.range_0 "y" PPI.Stream
  in
  let a: Ast.ast = Ast.ALet R.range_0 "y" PPI.Stream int_ty def body in
  let tm = L.lower env a in
  [ mk_sigelt "smoke_let_stream" (`(PXB.exp PPS.table [PSSB.shallow int] (PSSB.shallow int))) tm ]

%splice[smoke_let_stream] (_smoke_let_stream_sigelts ())
