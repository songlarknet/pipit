module Plugin.Test.Bug.MasterModes.V2b.SpliceLike

module PXB = Pipit.Exp.Base
module PPS = Pipit.Prim.Shallow
module PPT = Pipit.Prim.Table
module PSHS = Pipit.Prim.HasStream

open Plugin.Test.Bug.MasterModes.Types
open FStar.Pervasives.Native

#set-options "--warn_error -242"

unfold let __xprim_mm_v2b_opt_eq_int_46 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_Equality")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow (option master_index_int))
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow (option master_index_int))
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_Equality

unfold let __xprim_mm_v2b_opt_eq_int_45 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_disEquality")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow error_severity)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow error_severity)
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_disEquality

unfold let __xprim_mm_v2b_opt_eq_int_44 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "FStar.Pervasives.Native.uu___is_Some")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow (option master_index_int))
      (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool)))
  Some?

unfold let __xprim_mm_v2b_opt_eq_int_43 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_AmpAmp")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow bool)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow bool)
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_AmpAmp

unfold let __xprim_mm_v2b_opt_eq_int_42 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_Equality")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow master_mode)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow master_mode)
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_Equality

unfold let __xprim_mm_v2b_opt_eq_int_41 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_Equality")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow error_severity)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow error_severity)
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_Equality

unfold let __xprim_mm_v2b_opt_eq_int_40 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_Equality")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow mode)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow mode)
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_Equality

unfold let __xprim_mm_v2b_opt_eq_int_39 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "Prims.op_BarBar")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow bool)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow bool)
          (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow bool))))
  op_BarBar

unfold let __xprim_mm_v2b_opt_eq_int_38 : Pipit.Prim.Shallow.prim =
  Pipit.Prim.Shallow.Mkprim (Some "PipitRuntime.Prim.p'select")
  (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow bool)
      (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow master_mode)
          (Pipit.Prim.Table.FTFun (Pipit.Prim.HasStream.shallow master_mode)
              (Pipit.Prim.Table.FTVal (Pipit.Prim.HasStream.shallow master_mode)))))
  PipitRuntime.Prim.p'select

let mm_v2b_opt_eq_int_core (cfg: config_int) : Pipit.Exp.Base.exp Pipit.Prim.Shallow.table
  [Pipit.Prim.HasStream.shallow (option master_index_int);
   Pipit.Prim.HasStream.shallow error_severity;
   Pipit.Prim.HasStream.shallow mode]
  (Pipit.Prim.HasStream.shallow master_mode) =
  (fun master_enable ->
      (fun master_idx ->
          Pipit.Exp.Base.XLet (Pipit.Prim.HasStream.shallow master_mode)
            (Pipit.Exp.Base.XMu
              (Pipit.Exp.Base.XLet (Pipit.Prim.HasStream.shallow master_mode)
                  (Pipit.Exp.Base.XFby Master_Off (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XBVar 0)))
                  (Pipit.Exp.Base.XApps
                    (Pipit.Exp.Base.XApp
                        (Pipit.Exp.Base.XApp
                            (Pipit.Exp.Base.XApp
                                (Pipit.Exp.Base.XPrim
                                  __xprim_mm_v2b_opt_eq_int_38)
                                (Pipit.Exp.Base.XApps
                                  (Pipit.Exp.Base.XApp
                                      (Pipit.Exp.Base.XApp
                                          (Pipit.Exp.Base.XPrim
                                            __xprim_mm_v2b_opt_eq_int_39
                                          )
                                          (Pipit.Exp.Base.XApps
                                            (Pipit.Exp.Base.XApp
                                                (Pipit.Exp.Base.XApp
                                                    (Pipit.Exp.Base.XPrim
                                                      __xprim_mm_v2b_opt_eq_int_40
                                                    )
                                                    (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XBVar 4)))
                                                (Pipit.Exp.Base.XBase
                                                  (Pipit.Exp.Base.XVal Mode_Configure)))))
                                      (Pipit.Exp.Base.XApps
                                        (Pipit.Exp.Base.XApp
                                            (Pipit.Exp.Base.XApp
                                                (Pipit.Exp.Base.XPrim
                                                  __xprim_mm_v2b_opt_eq_int_41
                                                ) (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XBVar 3)))
                                            (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XVal S3_Severe))))
                                  ))) (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XVal Master_Off)))
                        (Pipit.Exp.Base.XApps
                          (Pipit.Exp.Base.XApp
                              (Pipit.Exp.Base.XApp
                                  (Pipit.Exp.Base.XApp
                                      (Pipit.Exp.Base.XPrim
                                        __xprim_mm_v2b_opt_eq_int_38
                                      )
                                      (Pipit.Exp.Base.XApps
                                        (Pipit.Exp.Base.XApp
                                            (Pipit.Exp.Base.XApp
                                                (Pipit.Exp.Base.XPrim
                                                  __xprim_mm_v2b_opt_eq_int_42
                                                ) (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XBVar 0)))
                                            (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XVal Master_Off)))
                                      ))
                                  (Pipit.Exp.Base.XApps
                                    (Pipit.Exp.Base.XApp
                                        (Pipit.Exp.Base.XApp
                                            (Pipit.Exp.Base.XApp
                                                (Pipit.Exp.Base.XPrim
                                                  __xprim_mm_v2b_opt_eq_int_38
                                                )
                                                (Pipit.Exp.Base.XApps
                                                  (Pipit.Exp.Base.XApp
                                                      (Pipit.Exp.Base.XApp
                                                          (Pipit.Exp.Base.XPrim
                                                            __xprim_mm_v2b_opt_eq_int_43
                                                          )
                                                          (Pipit.Exp.Base.XApps
                                                            (Pipit.Exp.Base.XApp
                                                                (Pipit.Exp.Base.XPrim
                                                                  __xprim_mm_v2b_opt_eq_int_44
                                                                )
                                                                (Pipit.Exp.Base.XBase
                                                                  (Pipit.Exp.Base.XBVar 2)))))
                                                      (Pipit.Exp.Base.XBase
                                                        (Pipit.Exp.Base.XVal
                                                          (op_Negation master_enable))))))
                                            (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XVal Follower)))
                                        (Pipit.Exp.Base.XApps
                                          (Pipit.Exp.Base.XApp
                                              (Pipit.Exp.Base.XApp
                                                  (Pipit.Exp.Base.XApp
                                                      (Pipit.Exp.Base.XPrim
                                                        __xprim_mm_v2b_opt_eq_int_38
                                                      )
                                                      (Pipit.Exp.Base.XApps
                                                        (Pipit.Exp.Base.XApp
                                                            (Pipit.Exp.Base.XApp
                                                                (Pipit.Exp.Base.XPrim
                                                                  __xprim_mm_v2b_opt_eq_int_43
                                                                )
                                                                (Pipit.Exp.Base.XApps
                                                                  (Pipit.Exp.Base.XApp
                                                                      (Pipit.Exp.Base.XApp
                                                                          (Pipit.Exp.Base.XPrim
                                                                            __xprim_mm_v2b_opt_eq_int_43
                                                                          )
                                                                          (Pipit.Exp.Base.XApps
                                                                            (Pipit.Exp.Base.XApp
                                                                                (Pipit.Exp.Base.XPrim
                                                                                  __xprim_mm_v2b_opt_eq_int_44
                                                                                )
                                                                                (Pipit.Exp.Base.XBase
                                                                                  (Pipit.Exp.Base.XBVar
                                                                                    2)))))
                                                                      (Pipit.Exp.Base.XBase
                                                                        (Pipit.Exp.Base.XVal
                                                                          master_enable)))))
                                                            (Pipit.Exp.Base.XApps
                                                              (Pipit.Exp.Base.XApp
                                                                  (Pipit.Exp.Base.XApp
                                                                      (Pipit.Exp.Base.XPrim
                                                                        __xprim_mm_v2b_opt_eq_int_45
                                                                      )
                                                                      (Pipit.Exp.Base.XBase
                                                                        (Pipit.Exp.Base.XBVar 3)))
                                                                  (Pipit.Exp.Base.XBase
                                                                    (Pipit.Exp.Base.XVal S2_Error)))
                                                            ))))
                                                  (Pipit.Exp.Base.XApps
                                                    (Pipit.Exp.Base.XApp
                                                        (Pipit.Exp.Base.XApp
                                                            (Pipit.Exp.Base.XApp
                                                                (Pipit.Exp.Base.XPrim
                                                                  __xprim_mm_v2b_opt_eq_int_38
                                                                )
                                                                (Pipit.Exp.Base.XApps
                                                                  (Pipit.Exp.Base.XApp
                                                                      (Pipit.Exp.Base.XApp
                                                                          (Pipit.Exp.Base.XPrim
                                                                            __xprim_mm_v2b_opt_eq_int_46
                                                                          )
                                                                          (Pipit.Exp.Base.XBase
                                                                            (Pipit.Exp.Base.XBVar 2)
                                                                          ))
                                                                      (Pipit.Exp.Base.XBase
                                                                        (Pipit.Exp.Base.XVal
                                                                          (Some master_idx))))))
                                                            (Pipit.Exp.Base.XBase
                                                              (Pipit.Exp.Base.XVal Current_Master)))
                                                        (Pipit.Exp.Base.XBase
                                                          (Pipit.Exp.Base.XVal Backup_Master)))))
                                              (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XVal Master_Off)
                                              )))))) (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XBVar 0))
                          ))))))
            (Pipit.Exp.Base.XBase (Pipit.Exp.Base.XBVar 0))) cfg.master_idx) cfg.master_enable