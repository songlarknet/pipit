(* "Literal" hand-written V2b core: matches the lifter's output term
   shape as closely as possible — no helpers, no top-level [unfold]
   prim definitions, inline [mkPrim] at every site, inline
   [Pipit.Prim.HasStream.shallow X] at every site.  This is the actual
   shape printed in /tmp/v2b.out.

   If this file verifies fast: the lifter shape per se is fine and
   something else (e.g. attributes, sigelt qualifiers, `_lifted`
   marker, [NoExtract] qual) makes F* slow.

   If this file explodes: it's the inline [mkPrim] (which is a regular
   [let] and won't unfold for field projection) causing F* to do
   thousands of unification attempts. Fix would then be to mark
   [Pipit.Prim.Shallow.mkPrim] as [unfold] OR have the lifter emit
   a top-level [unfold let _xprim_N ...] for each unique prim. *)
module Plugin.Test.Bug.MasterModes.V2b.Literal

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

module PXB  = Pipit.Exp.Base
module PPT  = Pipit.Prim.Table
module PPS  = Pipit.Prim.Shallow
module PSSB = Pipit.Prim.HasStream
module PRP  = PipitRuntime.Prim

#set-options "--warn_error -242"

(* The signature exactly matches what the lifter emits — no aliases. *)
let mm_v2b_literal_core (cfg: config_int):
  PXB.exp PPS.table
    [PSSB.shallow (option master_index_int);
     PSSB.shallow error_severity;
     PSSB.shallow mode]
    (PSSB.shallow master_mode)
  =
  let master_enable = cfg.master_enable in
  let master_idx    = cfg.master_idx    in
  PXB.XLet (PSSB.shallow master_mode)
    (PXB.XMu
      (PXB.XLet (PSSB.shallow master_mode)
        (PXB.XFby Master_Off (PXB.XBase (PXB.XBVar 0)))
        (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp
          (PXB.XPrim
            (PPS.mkPrim (Some "PipitRuntime.Prim.p'select")
              (PPT.FTFun (PSSB.shallow bool)
                (PPT.FTFun (PSSB.shallow master_mode)
                  (PPT.FTFun (PSSB.shallow master_mode)
                    (PPT.FTVal (PSSB.shallow master_mode)))))
              PRP.p'select))
          (PXB.XApps (PXB.XApp (PXB.XApp
            (PXB.XPrim
              (PPS.mkPrim (Some "Prims.op_BarBar")
                (PPT.FTFun (PSSB.shallow bool)
                  (PPT.FTFun (PSSB.shallow bool)
                    (PPT.FTVal (PSSB.shallow bool))))
                op_BarBar))
            (PXB.XApps (PXB.XApp (PXB.XApp
              (PXB.XPrim
                (PPS.mkPrim (Some "Prims.op_Equality")
                  (PPT.FTFun (PSSB.shallow mode)
                    (PPT.FTFun (PSSB.shallow mode)
                      (PPT.FTVal (PSSB.shallow bool))))
                  op_Equality))
              (PXB.XBase (PXB.XBVar 4)))
              (PXB.XBase (PXB.XVal Mode_Configure)))))
            (PXB.XApps (PXB.XApp (PXB.XApp
              (PXB.XPrim
                (PPS.mkPrim (Some "Prims.op_Equality")
                  (PPT.FTFun (PSSB.shallow error_severity)
                    (PPT.FTFun (PSSB.shallow error_severity)
                      (PPT.FTVal (PSSB.shallow bool))))
                  op_Equality))
              (PXB.XBase (PXB.XBVar 3)))
              (PXB.XBase (PXB.XVal S3_Severe)))))))
          (PXB.XBase (PXB.XVal Master_Off)))
          (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp
            (PXB.XPrim
              (PPS.mkPrim (Some "PipitRuntime.Prim.p'select")
                (PPT.FTFun (PSSB.shallow bool)
                  (PPT.FTFun (PSSB.shallow master_mode)
                    (PPT.FTFun (PSSB.shallow master_mode)
                      (PPT.FTVal (PSSB.shallow master_mode)))))
                PRP.p'select))
            (PXB.XApps (PXB.XApp (PXB.XApp
              (PXB.XPrim
                (PPS.mkPrim (Some "Prims.op_Equality")
                  (PPT.FTFun (PSSB.shallow master_mode)
                    (PPT.FTFun (PSSB.shallow master_mode)
                      (PPT.FTVal (PSSB.shallow bool))))
                  op_Equality))
              (PXB.XBase (PXB.XBVar 0)))
              (PXB.XBase (PXB.XVal Master_Off)))))
            (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp
              (PXB.XPrim
                (PPS.mkPrim (Some "PipitRuntime.Prim.p'select")
                  (PPT.FTFun (PSSB.shallow bool)
                    (PPT.FTFun (PSSB.shallow master_mode)
                      (PPT.FTFun (PSSB.shallow master_mode)
                        (PPT.FTVal (PSSB.shallow master_mode)))))
                  PRP.p'select))
              (PXB.XApps (PXB.XApp (PXB.XApp
                (PXB.XPrim
                  (PPS.mkPrim (Some "Prims.op_AmpAmp")
                    (PPT.FTFun (PSSB.shallow bool)
                      (PPT.FTFun (PSSB.shallow bool)
                        (PPT.FTVal (PSSB.shallow bool))))
                    op_AmpAmp))
                (PXB.XApps (PXB.XApp
                  (PXB.XPrim
                    (PPS.mkPrim (Some "FStar.Pervasives.Native.uu___is_Some")
                      (PPT.FTFun (PSSB.shallow (option master_index_int))
                        (PPT.FTVal (PSSB.shallow bool)))
                      Some?))
                  (PXB.XBase (PXB.XBVar 2)))))
                (PXB.XBase (PXB.XVal (op_Negation master_enable))))))
              (PXB.XBase (PXB.XVal Follower)))
              (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp
                (PXB.XPrim
                  (PPS.mkPrim (Some "PipitRuntime.Prim.p'select")
                    (PPT.FTFun (PSSB.shallow bool)
                      (PPT.FTFun (PSSB.shallow master_mode)
                        (PPT.FTFun (PSSB.shallow master_mode)
                          (PPT.FTVal (PSSB.shallow master_mode)))))
                    PRP.p'select))
                (PXB.XApps (PXB.XApp (PXB.XApp
                  (PXB.XPrim
                    (PPS.mkPrim (Some "Prims.op_AmpAmp")
                      (PPT.FTFun (PSSB.shallow bool)
                        (PPT.FTFun (PSSB.shallow bool)
                          (PPT.FTVal (PSSB.shallow bool))))
                      op_AmpAmp))
                  (PXB.XApps (PXB.XApp (PXB.XApp
                    (PXB.XPrim
                      (PPS.mkPrim (Some "Prims.op_AmpAmp")
                        (PPT.FTFun (PSSB.shallow bool)
                          (PPT.FTFun (PSSB.shallow bool)
                            (PPT.FTVal (PSSB.shallow bool))))
                        op_AmpAmp))
                    (PXB.XApps (PXB.XApp
                      (PXB.XPrim
                        (PPS.mkPrim (Some "FStar.Pervasives.Native.uu___is_Some")
                          (PPT.FTFun (PSSB.shallow (option master_index_int))
                            (PPT.FTVal (PSSB.shallow bool)))
                          Some?))
                      (PXB.XBase (PXB.XBVar 2)))))
                    (PXB.XBase (PXB.XVal master_enable)))))
                  (PXB.XApps (PXB.XApp (PXB.XApp
                    (PXB.XPrim
                      (PPS.mkPrim (Some "Prims.op_disEquality")
                        (PPT.FTFun (PSSB.shallow error_severity)
                          (PPT.FTFun (PSSB.shallow error_severity)
                            (PPT.FTVal (PSSB.shallow bool))))
                        op_disEquality))
                    (PXB.XBase (PXB.XBVar 3)))
                    (PXB.XBase (PXB.XVal S2_Error)))))))
                (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp
                  (PXB.XPrim
                    (PPS.mkPrim (Some "PipitRuntime.Prim.p'select")
                      (PPT.FTFun (PSSB.shallow bool)
                        (PPT.FTFun (PSSB.shallow master_mode)
                          (PPT.FTFun (PSSB.shallow master_mode)
                            (PPT.FTVal (PSSB.shallow master_mode)))))
                      PRP.p'select))
                  (PXB.XApps (PXB.XApp (PXB.XApp
                    (PXB.XPrim
                      (PPS.mkPrim (Some "Prims.op_Equality")
                        (PPT.FTFun (PSSB.shallow (option master_index_int))
                          (PPT.FTFun (PSSB.shallow (option master_index_int))
                            (PPT.FTVal (PSSB.shallow bool))))
                        op_Equality))
                    (PXB.XBase (PXB.XBVar 2)))
                    (PXB.XBase (PXB.XVal (Some master_idx))))))
                  (PXB.XBase (PXB.XVal Current_Master)))
                  (PXB.XBase (PXB.XVal Backup_Master)))))
                (PXB.XBase (PXB.XVal Master_Off)))))))))
    (PXB.XBase (PXB.XBVar 0))
))))
