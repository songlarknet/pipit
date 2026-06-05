(* Hand-written equivalent of the core expression that the lifter emits
   for V2b. Reproduces the term printed in /tmp/v2b.out under
   `ast_core_sigelt def:`. Goal: answer "does F* explode on this core
   term itself, or is the lifter emitting something subtly different
   that triggers it?" *)
module Plugin.Test.Bug.MasterModes.V2b.ManualNoWrap

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

module PXB  = Pipit.Exp.Base
module PPT  = Pipit.Prim.Table
module PPS  = Pipit.Prim.Shallow
module PSSB = Pipit.Prim.HasStream
module PRP  = PipitRuntime.Prim

#set-options "--warn_error -242"

(* shorthand for the shallow types involved *)
let sh_bool = PSSB.shallow bool
let sh_mode = PSSB.shallow mode
let sh_es   = PSSB.shallow error_severity
let sh_mm   = PSSB.shallow master_mode
let sh_omi  = PSSB.shallow (option master_index_int)

(* The cexp context (matches lifter, innermost first):
     index 0 = ref_msg, 1 = error, 2 = mode_                            *)
let ctx_outer : list PPS.shallow_type = [sh_omi; sh_es; sh_mode]

(* Inside the inner XLet body the ctx has [pre_master; master_mode_;
   ref_msg; error; mode_], so:
     index 0 = pre_master, 1 = master_mode_, 2 = ref_msg, 3 = error, 4 = mode_ *)
let ctx_inner : list PPS.shallow_type =
  sh_mm :: sh_mm :: ctx_outer

(* --- exp aliases at the two relevant contexts ----------------------- *)
unfold let eo_mm = PXB.exp PPS.table ctx_outer sh_mm
unfold let ei_mm = PXB.exp PPS.table ctx_inner sh_mm
unfold let ei_b  = PXB.exp PPS.table ctx_inner sh_bool

(* Wrapper so F* pins the table/context implicits on each XPrim. *)

(* Primitive definitions at top level, [unfold] so F* sees the concrete
   prim_ty at every use site.  We use record syntax (rather than
   [mkPrim]) so that the field projection [prim_ty] reduces without
   needing [mkPrim] itself to be marked unfold. *)
unfold let sel_mm : PPS.prim = {
  prim_id  = Some "PipitRuntime.Prim.p'select";
  prim_ty  = PPT.FTFun sh_bool (PPT.FTFun sh_mm (PPT.FTFun sh_mm (PPT.FTVal sh_mm)));
  prim_sem = PRP.p'select;
}

unfold let bb : PPS.prim = {
  prim_id  = Some "Prims.op_BarBar";
  prim_ty  = PPT.FTFun sh_bool (PPT.FTFun sh_bool (PPT.FTVal sh_bool));
  prim_sem = op_BarBar;
}

unfold let aa : PPS.prim = {
  prim_id  = Some "Prims.op_AmpAmp";
  prim_ty  = PPT.FTFun sh_bool (PPT.FTFun sh_bool (PPT.FTVal sh_bool));
  prim_sem = op_AmpAmp;
}

unfold let eq_mode : PPS.prim = {
  prim_id  = Some "Prims.op_Equality";
  prim_ty  = PPT.FTFun sh_mode (PPT.FTFun sh_mode (PPT.FTVal sh_bool));
  prim_sem = op_Equality;
}

unfold let eq_es : PPS.prim = {
  prim_id  = Some "Prims.op_Equality";
  prim_ty  = PPT.FTFun sh_es (PPT.FTFun sh_es (PPT.FTVal sh_bool));
  prim_sem = op_Equality;
}

unfold let neq_es : PPS.prim = {
  prim_id  = Some "Prims.op_disEquality";
  prim_ty  = PPT.FTFun sh_es (PPT.FTFun sh_es (PPT.FTVal sh_bool));
  prim_sem = op_disEquality;
}

unfold let eq_mm : PPS.prim = {
  prim_id  = Some "Prims.op_Equality";
  prim_ty  = PPT.FTFun sh_mm (PPT.FTFun sh_mm (PPT.FTVal sh_bool));
  prim_sem = op_Equality;
}

unfold let eq_omi : PPS.prim = {
  prim_id  = Some "Prims.op_Equality";
  prim_ty  = PPT.FTFun sh_omi (PPT.FTFun sh_omi (PPT.FTVal sh_bool));
  prim_sem = op_Equality;
}

unfold let is_some : PPS.prim = {
  prim_id  = Some "FStar.Pervasives.Native.uu___is_Some";
  prim_ty  = PPT.FTFun sh_omi (PPT.FTVal sh_bool);
  prim_sem = Some?;
}



let mm_v2b_manual_core (cfg: config_int): eo_mm =
  let master_enable = cfg.master_enable in
  let master_idx    = cfg.master_idx    in

  // p2 p a b = XApps (XApp (XApp (XPrim p) a) b)
  // p3 p a b c = XApps (XApp (XApp (XApp (XPrim p) a) b) c)

  // cond1 : mode_ = Mode_Configure || error = S3_Severe
  let cond1 : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner bb)
      (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner eq_mode) (PXB.XBase (PXB.XBVar 4))) (PXB.XBase (PXB.XVal Mode_Configure)))))
      (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner eq_es) (PXB.XBase (PXB.XBVar 3))) (PXB.XBase (PXB.XVal S3_Severe)))))
  in
  // cond_pre0 : pre_master = Master_Off
  let cond_pre0 : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner eq_mm) (PXB.XBase (PXB.XBVar 0))) (PXB.XBase (PXB.XVal Master_Off)))
  in
  // cond_follower : Some? ref_msg && not master_enable
  let cond_follower : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner aa)
      (PXB.XApps (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner is_some) (PXB.XBase (PXB.XBVar 2)))))
      (PXB.XBase (PXB.XVal (op_Negation master_enable))))
  in
  // cond_main : Some? ref_msg && master_enable && error <> S2_Error
  let cond_main : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner aa)
      (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner aa)
        (PXB.XApps (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner is_some) (PXB.XBase (PXB.XBVar 2)))))
        (PXB.XBase (PXB.XVal master_enable)))))
      (PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner neq_es) (PXB.XBase (PXB.XBVar 3))) (PXB.XBase (PXB.XVal S2_Error)))))
  in
  // cond_eq_some : ref_msg = Some master_idx
  let cond_eq_some : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner eq_omi) (PXB.XBase (PXB.XBVar 2))) (PXB.XBase (PXB.XVal (Some master_idx))))
  in

  // innermost: if ref_msg = Some master_idx then Current_Master else Backup_Master
  let body_eq_some : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner sel_mm)
      cond_eq_some) (PXB.XBase (PXB.XVal Current_Master))) (PXB.XBase (PXB.XVal Backup_Master)))
  in
  // body_main : if cond_main then body_eq_some else Master_Off
  let body_main : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner sel_mm)
      cond_main) body_eq_some) (PXB.XBase (PXB.XVal Master_Off)))
  in
  // body_pre0_then : if cond_follower then Follower else body_main
  let body_pre0_then : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner sel_mm)
      cond_follower) (PXB.XBase (PXB.XVal Follower))) body_main)
  in
  // body_pre0 : if pre_master = Master_Off then body_pre0_then else pre_master
  let body_pre0 : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner sel_mm)
      cond_pre0) body_pre0_then) (PXB.XBase (PXB.XBVar 0)))
  in
  // body_inner : if cond1 then Master_Off else body_pre0
  let body_inner : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (PXB.XPrim #PPS.table #ctx_inner sel_mm)
      cond1) (PXB.XBase (PXB.XVal Master_Off))) body_pre0)
  in

  // inner XLet binds pre_master = Master_Off `fby` master_mode_
  let mu_body : PXB.exp PPS.table (sh_mm :: ctx_outer) sh_mm =
    PXB.XLet sh_mm
      (PXB.XFby Master_Off (PXB.XBase (PXB.XBVar 0)))
      body_inner
  in
  // outer XLet binds master_mode_ = rec ...
  PXB.XLet sh_mm
    (PXB.XMu mu_body)
    (PXB.XBase (PXB.XBVar 0))
