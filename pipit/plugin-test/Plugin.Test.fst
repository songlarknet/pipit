module Plugin.Test
#lang-pipit

#set-options "--ext pipit:lift:debug"
#set-options "--print_implicits --print_bound_var_types --print_full_names"

open Pipit.Plugin.Primitives
module PSSB = Pipit.Sugar.Shallow.Base

instance has_stream_int: PSSB.has_stream int = {
  ty_id       = [`%Prims.int];
  val_default = 0;
}
// mutual recursion not supported:

// let fst (#a #b: eqtype) {| PSSB.has_stream a |} {| PSSB.has_stream b |} (x: stream (a & b)): stream a =
//   fst x

// let snd (#a #b: eqtype) {| PSSB.has_stream a |} {| PSSB.has_stream b |} (x: stream (a & b)): stream b =
//   snd x

let plus (a b: stream int) = a + b
let sub (a b: stream int) = a - b

// let shint = Pipit.Sugar.Shallow.Base.shallow Prims.int
// let shiiu = (Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)))
// let shiu = (Pipit.Sugar.Shallow.Base.shallow (Prims.int & Prims.unit))
// let shu = Pipit.Sugar.Shallow.Base.shallow Prims.unit


// let eg_letrec_mut_core_simpx = fun (ctx30421: Pipit.Prim.Table.context Pipit.Prim.Shallow.table) ->
//   fun
//     (x30422:
//       Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//         ctx30421
//         shint)
//     ->
//     Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//       shiiu
//       (Pipit.Exp.Base.XMu #Pipit.Prim.Shallow.table
//           (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//               shint
//               (Plugin.Test.Language.Lift.fst_ppt_core0 (shiiu ::
//                     ctx30421)
//                   #Prims.int
//                   #(Prims.int & Prims.unit)
//                   #Plugin.Test.Language.Lift.has_stream_int
//                   #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                       #Prims.unit
//                       #Plugin.Test.Language.Lift.has_stream_int
//                       #Pipit.Sugar.Shallow.Base.has_stream_unit)
//                   (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                       (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//               (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//                   shint
//                   (Plugin.Test.Language.Lift.fst_ppt_core0 
//                   (shint
//                          ::
//                         shiiu ::
//                         ctx30421)
//                       #Prims.int
//                       #Prims.unit
//                       #Plugin.Test.Language.Lift.has_stream_int
//                       #Pipit.Sugar.Shallow.Base.has_stream_unit
//                       (Plugin.Test.Language.Lift.snd_ppt_core1 (shint
//                              ::
//                             shiiu ::
//                             ctx30421)
//                           #Prims.int
//                           #(Prims.int & Prims.unit)
//                           #Plugin.Test.Language.Lift.has_stream_int
//                           #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                               #Prims.unit
//                               #Plugin.Test.Language.Lift.has_stream_int
//                               #Pipit.Sugar.Shallow.Base.has_stream_unit)
//                           (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                               (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1))))
//                   (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//                       shint
//                       (Plugin.Test.Language.Lift.plus_ppt_core2 (shint
//                              ::
//                             shint ::
//                             shiiu ::
//                             ctx30421)
//                           (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                               #_
//                               #ctx30421
//                               x30422
//                               [
//                                 shint;
//                                 shint;
//                                 shiiu
//                               ])
//                           (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                               (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//                       (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//                           shint
//                           (Plugin.Test.Language.Lift.sub_ppt_core3 (shint ::
//                                 shint ::
//                                 shint ::
//                                 shiiu ::
//                                 ctx30421)
//                               (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                                   #_
//                                   #ctx30421
//                                   x30422
//                                   [
//                                     shint;
//                                     shint;
//                                     shint;
//                                     shiiu
//                                   ])
//                               (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                   (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//                           ((fun (ctx30428: Pipit.Prim.Table.context Pipit.Prim.Shallow.table) ->
//                                 fun
//                                   (prim30429:
//                                     Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                       ctx30428
//                                       shint)
//                                   ->
//                                   fun
//                                     (prim30430:
//                                       Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                         ctx30428
//                                         shiu)
//                                     ->
//                                     Pipit.Exp.Base.XApps #Pipit.Prim.Shallow.table
//                                       #_
//                                       #shiiu
//                                       (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                           #_
//                                           #shiu
//                                           (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                               #_
//                                               #shint
//                                               (Pipit.Exp.Base.XPrim #Pipit.Prim.Shallow.table
//                                                   (Pipit.Prim.Shallow.mkPrim FStar.Pervasives.Native.None
//                                                       (Pipit.Prim.Table.FTFun
//                                                           shint
//                                                           (Pipit.Prim.Table.FTFun
//                                                               shiu
//                                                               (Pipit.Prim.Table.FTVal
//                                                                 shiiu)))
//                                                       (fun (_130431: Prims.int) ->
//                                                           fun (_230432: Prims.int & Prims.unit) ->
//                                                             FStar.Pervasives.Native.Mktuple2
//                                                               #Prims.int
//                                                               #(Prims.int & Prims.unit)
//                                                               _130431
//                                                               _230432)))
//                                               prim30429)
//                                           prim30430)) (shint ::
//                                 shint ::
//                                 shint ::
//                                 shint ::
//                                 shiiu ::
//                                 ctx30421)
//                               (Plugin.Test.Language.Lift.plus_ppt_core2 (shint ::
//                                     shint ::
//                                     shint ::
//                                     shint ::
//                                     shiiu ::
//                                     ctx30421)
//                                   (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                                       #_
//                                       #ctx30421
//                                       x30422
//                                       [
//                                         shint;
//                                         shint;
//                                         shint;
//                                         shint;
//                                         shiiu
//                                       ])
//                                   (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                       (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//                               ((fun (ctx30423: Pipit.Prim.Table.context Pipit.Prim.Shallow.table) ->
//                                     fun
//                                       (prim30424:
//                                         Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                           ctx30423
//                                           shint)
//                                       ->
//                                       fun
//                                         (prim30425:
//                                           Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                             ctx30423
//                                             shu)
//                                         ->
//                                         Pipit.Exp.Base.XApps #Pipit.Prim.Shallow.table
//                                           #_
//                                           #shiu
//                                           (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                               #_
//                                               #shu
//                                               (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                                   #_
//                                                   #shint
//                                                   (Pipit.Exp.Base.XPrim #Pipit.Prim.Shallow.table
//                                                       (Pipit.Prim.Shallow.mkPrim FStar.Pervasives.Native.None
//                                                           (Pipit.Prim.Table.FTFun
//                                                               shint
//                                                               (Pipit.Prim.Table.FTFun
//                                                                   shu
//                                                                   (Pipit.Prim.Table.FTVal
//                                                                     shiu)))
//                                                           (fun (_130426: Prims.int) ->
//                                                               fun (_230427: Prims.unit) ->
//                                                                 FStar.Pervasives.Native.Mktuple2
//                                                                   #Prims.int
//                                                                   #Prims.unit
//                                                                   _130426
//                                                                   _230427)))
//                                                   prim30424)
//                                               prim30425)) (shint
//                                      ::
//                                     shint ::
//                                     shint ::
//                                     shint ::
//                                     shiiu ::
//                                     ctx30421)
//                                   (Plugin.Test.Language.Lift.sub_ppt_core3 (shint ::
//                                         shint ::
//                                         shint ::
//                                         shint ::
//                                         shiiu ::
//                                         ctx30421)
//                                       (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                                           #_
//                                           #ctx30421
//                                           x30422
//                                           [
//                                             shint;
//                                             shint;
//                                             shint;
//                                             shint;
//                                             shiiu
//                                           ])
//                                       (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                           (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1)))
//                                   (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                       (Pipit.Exp.Base.XVal #Pipit.Prim.Shallow.table ())))))))))
//       (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//           shint
//           (Plugin.Test.Language.Lift.fst_ppt_core0 (shiiu ::
//                 ctx30421)
//               #Prims.int
//               #(Prims.int & Prims.unit)
//               #Plugin.Test.Language.Lift.has_stream_int
//               #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                   #Prims.unit
//                   #Plugin.Test.Language.Lift.has_stream_int
//                   #Pipit.Sugar.Shallow.Base.has_stream_unit)
//               (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                   (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//           (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//               shint
//               (Plugin.Test.Language.Lift.fst_ppt_core0 (shint ::
//                     shiiu ::
//                     ctx30421)
//                   #Prims.int
//                   #Prims.unit
//                   #Plugin.Test.Language.Lift.has_stream_int
//                   #Pipit.Sugar.Shallow.Base.has_stream_unit
//                   (Plugin.Test.Language.Lift.snd_ppt_core1 (shint
//                          ::
//                         shiiu ::
//                         ctx30421)
//                       #Prims.int
//                       #(Prims.int & Prims.unit)
//                       #Plugin.Test.Language.Lift.has_stream_int
//                       #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                           #Prims.unit
//                           #Plugin.Test.Language.Lift.has_stream_int
//                           #Pipit.Sugar.Shallow.Base.has_stream_unit)
//                       (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                           (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1))))
//               (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                   (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1))))

// let eg_letrec_core_orig =  fun (ctx30421: Pipit.Prim.Table.context Pipit.Prim.Shallow.table) ->
//   fun
//     (x30422:
//       Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//         ctx30421
//         (Pipit.Sugar.Shallow.Base.shallow Prims.int))
//     ->
//     Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//       (Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)))
//       (Pipit.Exp.Base.XMu #Pipit.Prim.Shallow.table
//           (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//               (Pipit.Sugar.Shallow.Base.shallow Prims.int)
//               (Plugin.Test.Language.Lift.fst_ppt_core0 (Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                         (Prims.int & Prims.unit)) ::
//                     ctx30421)
//                   #Prims.int
//                   #(Prims.int & Prims.unit)
//                   #Plugin.Test.Language.Lift.has_stream_int
//                   #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                       #Prims.unit
//                       #Plugin.Test.Language.Lift.has_stream_int
//                       #Pipit.Sugar.Shallow.Base.has_stream_unit)
//                   (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                       (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//               (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//                   (Pipit.Sugar.Shallow.Base.shallow Prims.int)
//                   (Plugin.Test.Language.Lift.fst_ppt_core0 (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                          ::
//                         Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)) ::
//                         ctx30421)
//                       #Prims.int
//                       #Prims.unit
//                       #Plugin.Test.Language.Lift.has_stream_int
//                       #Pipit.Sugar.Shallow.Base.has_stream_unit
//                       (Plugin.Test.Language.Lift.snd_ppt_core1 (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                              ::
//                             Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)) ::
//                             ctx30421)
//                           #Prims.int
//                           #(Prims.int & Prims.unit)
//                           #Plugin.Test.Language.Lift.has_stream_int
//                           #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                               #Prims.unit
//                               #Plugin.Test.Language.Lift.has_stream_int
//                               #Pipit.Sugar.Shallow.Base.has_stream_unit)
//                           (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                               (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1))))
//                   (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//                       (Pipit.Sugar.Shallow.Base.shallow Prims.int)
//                       (Plugin.Test.Language.Lift.plus_ppt_core2 (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                              ::
//                             Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                             Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)) ::
//                             ctx30421)
//                           (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                               #_
//                               #ctx30421
//                               x30422
//                               [
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                 Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                     (Prims.int & Prims.unit))
//                               ])
//                           (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                               (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//                       (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//                           (Pipit.Sugar.Shallow.Base.shallow Prims.int)
//                           (Plugin.Test.Language.Lift.sub_ppt_core3 (Pipit.Sugar.Shallow.Base.shallow
//                                   Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                     (Prims.int & Prims.unit)) ::
//                                 ctx30421)
//                               (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                                   #_
//                                   #ctx30421
//                                   x30422
//                                   [
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                     Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                         (Prims.int & Prims.unit))
//                                   ])
//                               (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                   (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//                           ((fun (ctx30428: Pipit.Prim.Table.context Pipit.Prim.Shallow.table) ->
//                                 fun
//                                   (prim30429:
//                                     Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                       ctx30428
//                                       (Pipit.Sugar.Shallow.Base.shallow Prims.int))
//                                   ->
//                                   fun
//                                     (prim30430:
//                                       Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                         ctx30428
//                                         (Pipit.Sugar.Shallow.Base.shallow (Prims.int & Prims.unit)))
//                                     ->
//                                     Pipit.Exp.Base.XApps #Pipit.Prim.Shallow.table
//                                       #_
//                                       #(Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                             (Prims.int & Prims.unit)))
//                                       (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                           #_
//                                           #(Pipit.Sugar.Shallow.Base.shallow (Prims.int & Prims.unit
//                                               ))
//                                           (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                               #_
//                                               #(Pipit.Sugar.Shallow.Base.shallow Prims.int)
//                                               (Pipit.Exp.Base.XPrim #Pipit.Prim.Shallow.table
//                                                   (Pipit.Prim.Shallow.mkPrim FStar.Pervasives.Native.None
//                                                       (Pipit.Prim.Table.FTFun
//                                                           (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                                                             )
//                                                           (Pipit.Prim.Table.FTFun
//                                                               (Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                                                     Prims.unit))
//                                                               (Pipit.Prim.Table.FTVal
//                                                                 (Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                                                       (Prims.int & Prims.unit))))))
//                                                       (fun (_130431: Prims.int) ->
//                                                           fun (_230432: Prims.int & Prims.unit) ->
//                                                             FStar.Pervasives.Native.Mktuple2
//                                                               #Prims.int
//                                                               #(Prims.int & Prims.unit)
//                                                               _130431
//                                                               _230432)))
//                                               prim30429)
//                                           prim30430)) (Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                 Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                     (Prims.int & Prims.unit)) ::
//                                 ctx30421)
//                               (Plugin.Test.Language.Lift.plus_ppt_core2 (Pipit.Sugar.Shallow.Base.shallow
//                                       Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                         (Prims.int & Prims.unit)) ::
//                                     ctx30421)
//                                   (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                                       #_
//                                       #ctx30421
//                                       x30422
//                                       [
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                         Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                             (Prims.int & Prims.unit))
//                                       ])
//                                   (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                       (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//                               ((fun (ctx30423: Pipit.Prim.Table.context Pipit.Prim.Shallow.table) ->
//                                     fun
//                                       (prim30424:
//                                         Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                           ctx30423
//                                           (Pipit.Sugar.Shallow.Base.shallow Prims.int))
//                                       ->
//                                       fun
//                                         (prim30425:
//                                           Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//                                             ctx30423
//                                             (Pipit.Sugar.Shallow.Base.shallow Prims.unit))
//                                         ->
//                                         Pipit.Exp.Base.XApps #Pipit.Prim.Shallow.table
//                                           #_
//                                           #(Pipit.Sugar.Shallow.Base.shallow (Prims.int & Prims.unit
//                                               ))
//                                           (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                               #_
//                                               #(Pipit.Sugar.Shallow.Base.shallow Prims.unit)
//                                               (Pipit.Exp.Base.XApp #Pipit.Prim.Shallow.table
//                                                   #_
//                                                   #(Pipit.Sugar.Shallow.Base.shallow Prims.int)
//                                                   (Pipit.Exp.Base.XPrim #Pipit.Prim.Shallow.table
//                                                       (Pipit.Prim.Shallow.mkPrim FStar.Pervasives.Native.None
//                                                           (Pipit.Prim.Table.FTFun
//                                                               (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                                                                 )
//                                                               (Pipit.Prim.Table.FTFun
//                                                                   (Pipit.Sugar.Shallow.Base.shallow Prims.unit
//                                                                     )
//                                                                   (Pipit.Prim.Table.FTVal
//                                                                     (Pipit.Sugar.Shallow.Base.shallow
//                                                                         (Prims.int & Prims.unit)))))
//                                                           (fun (_130426: Prims.int) ->
//                                                               fun (_230427: Prims.unit) ->
//                                                                 FStar.Pervasives.Native.Mktuple2
//                                                                   #Prims.int
//                                                                   #Prims.unit
//                                                                   _130426
//                                                                   _230427)))
//                                                   prim30424)
//                                               prim30425)) (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                                      ::
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                     Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                         (Prims.int & Prims.unit)) ::
//                                     ctx30421)
//                                   (Plugin.Test.Language.Lift.sub_ppt_core3 (Pipit.Sugar.Shallow.Base.shallow
//                                           Prims.int ::
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                         Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                                         Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                             (Prims.int & Prims.unit)) ::
//                                         ctx30421)
//                                       (Pipit.Exp.Binding.lifts #Pipit.Prim.Shallow.table
//                                           #_
//                                           #ctx30421
//                                           x30422
//                                           [
//                                             Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                             Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                             Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                             Pipit.Sugar.Shallow.Base.shallow Prims.int;
//                                             Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                                                 (Prims.int & Prims.unit))
//                                           ])
//                                       (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                           (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1)))
//                                   (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                                       (Pipit.Exp.Base.XVal #Pipit.Prim.Shallow.table ())))))))))
//       (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//           (Pipit.Sugar.Shallow.Base.shallow Prims.int)
//           (Plugin.Test.Language.Lift.fst_ppt_core0 (Pipit.Sugar.Shallow.Base.shallow (Prims.int &
//                     (Prims.int & Prims.unit)) ::
//                 ctx30421)
//               #Prims.int
//               #(Prims.int & Prims.unit)
//               #Plugin.Test.Language.Lift.has_stream_int
//               #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                   #Prims.unit
//                   #Plugin.Test.Language.Lift.has_stream_int
//                   #Pipit.Sugar.Shallow.Base.has_stream_unit)
//               (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                   (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 0)))
//           (Pipit.Exp.Base.XLet #Pipit.Prim.Shallow.table
//               (Pipit.Sugar.Shallow.Base.shallow Prims.int)
//               (Plugin.Test.Language.Lift.fst_ppt_core0 (Pipit.Sugar.Shallow.Base.shallow Prims.int ::
//                     Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)) ::
//                     ctx30421)
//                   #Prims.int
//                   #Prims.unit
//                   #Plugin.Test.Language.Lift.has_stream_int
//                   #Pipit.Sugar.Shallow.Base.has_stream_unit
//                   (Plugin.Test.Language.Lift.snd_ppt_core1 (Pipit.Sugar.Shallow.Base.shallow Prims.int
//                          ::
//                         Pipit.Sugar.Shallow.Base.shallow (Prims.int & (Prims.int & Prims.unit)) ::
//                         ctx30421)
//                       #Prims.int
//                       #(Prims.int & Prims.unit)
//                       #Plugin.Test.Language.Lift.has_stream_int
//                       #(Pipit.Sugar.Shallow.Base.has_stream_tup2 #Prims.int
//                           #Prims.unit
//                           #Plugin.Test.Language.Lift.has_stream_int
//                           #Pipit.Sugar.Shallow.Base.has_stream_unit)
//                       (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                           (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1))))
//               (Pipit.Exp.Base.XBase #Pipit.Prim.Shallow.table
//                   (Pipit.Exp.Base.XBVar #Pipit.Prim.Shallow.table 1))))
//     <:
//     Prims.Tot
//     (Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
//         ctx30421
//         (Pipit.Sugar.Shallow.Base.shallow Prims.int))

let eg_letrec_mut (x: stream int): stream int =
  let rec a = plus x b
      and b = sub x a
  in a


(*
let eg_inc_left_strm (x: stream int) =
  x + 1

let eg_inc_right_strm (x: stream int) =
  1 + x

let eg_additions_strm (x: stream int) =
  (x + x) + x

let eg_additions_strm_ret_ann (x: stream int): stream int =
  (x + x) + x

let eg_fby (x: stream int) =
  0 `fby` x

let eg_fby_inc (x: stream int) =
  0 `fby` x + 1

let eg_letrecfun (x: stream int): stream int =
  let rec count x = if x > 0 then count (x - 1) else 0 in
  count 0

let eg_let_strm (x: stream int) =
  let strm = x + 1 in
  strm + x

let eg_let_strm_ann (x: stream int): stream int =
  let strm: stream int = 1 in
  strm + x

let eg_let_stat (x: stream int): stream int =
  let stat = 1 in
  x + stat

let eg_rec_strm (x: stream int) =
  let rec count = 0 `fby` count + 1 in
  count

let eg_rec_strm_let_stat (x: stream int) =
  let rec count1 = 0 `fby` count1 + 1 in
  let static1: int = 0 in
  count1 + static1

let eg_mixed_ann (x: stream int) =
  let rec count1 = 0 `fby` count1 + 1 in
  let rec count2: stream int = 0 `fby` count2 + 1 in
  let strm1: stream int = 0 in
  let strm2: stream int = 0 in
  let strm3 = count1 + strm1 in
  let static1: int = 0 in
  let static2 = 0 in
  count1 + count2 + strm1 + strm2 + strm3 + static1 + static2

let eg_pairs (x: stream int) (y: stream bool): stream int =
  0 `fby` fst (x, y)

type ctor = | Ctor: x: int -> y: int -> ctor
instance has_stream_ctor: PSSB.has_stream ctor = {
  ty_id       = [`%ctor];
  val_default = Ctor PSSB.val_default PSSB.val_default;
}

let eg_ctor (add: stream int) =
  let rec rcd =
    let x = 0 `fby` Ctor?.x rcd + add in
    let y = 0 `fby` Ctor?.y rcd - add in
    Ctor x y
  in
  rcd

let eg_pairsrec (add: stream int) =
  let rec xy =
    let x = 0 `fby` fst xy + add in
    let y = 0 `fby` snd xy - add in
    (x, y)
  in
  xy

type record = { x: int; y: int; }

instance has_stream_record: PSSB.has_stream record = {
  ty_id       = [`%record];
  val_default = { x = 0; y = 0; };
}

let eg_record (add: stream int) =
  let x = 0 `fby` add in
  let y = 1 `fby` add in
  let xy = { x; y } in
  xy.x


// TODO match
// [@@source_mode (ModeFun Stream true Stream)]
// let eg_streaming_if (x: int) =
//   if x >= 0 then x else -x

// %splice[] (PPL.lift_tac1 "eg_streaming_if")

// let eg_streaming_match_lets (x: stream int): stream int =
//   let cond = x >= 0 in
//   let abs =
//     match cond with
//       | true -> x
//       | false -> -x
//   in abs

// %splice[] (autolift_binds [`%eg_streaming_match_lets])

let eg_static_match (consts: list int) (x: stream int) =
  match consts with
  | [] -> 0
  | (c: int) :: _ -> c + x

let silly_id (x: int): y: int { x == y } = x

let eg_refinement0 (x: stream int) =
  silly_id x

(*** Not supported examples ***)


// streaming matches cannot bind variables:

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_match_bind (x: stream (option int)): stream int =
//   match x with
//   | Some e -> e
//   | None -> 0

// [@@Tac.preprocess_with tac_lift]
// let eg_streaming_letmatch (xy: stream (int & int)): stream int =
//   let (x, y) = xy in
//   x + y

// Lemma instantiation not supported; use a pattern instead
// let lemma_nat_something (x: int) (y: int): Lemma (ensures x > y) = admit ()

// let eg_instantiate_lemma (x y: stream int): stream int =
//   lemma_nat_something x y;
//   x + y

// %splice[] (autolift_binds [`%eg_instantiate_lemma])


*)