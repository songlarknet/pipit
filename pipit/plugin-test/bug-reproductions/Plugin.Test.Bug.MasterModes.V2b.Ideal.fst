(* "Ideal" hand-written core for V2b: same observable behaviour as
   [Plugin.Test.Bug.MasterModes.V2b.Manual] but reshaped the way a
   smarter lifter SHOULD emit it:

   1. CSE: [Some? ref_msg] is computed once in an XLet and reused.
      The source-level program writes it 3 times (lines for Follower,
      cond_main, and implicitly through [ref_msg = Some master_idx]
      which also needs the tag check).
   2. The "is = Some master_idx" check is rewritten as
        is_some && Some?.v ref_msg = master_idx
      so the equality is on [int] (cheap eqtype) rather than on
      [option master_index_int] (induces SMT-time derivation of
      [hasEq (option master_index_int)]).
   3. The branch on [cond_off] short-circuits the whole subtree —
      we keep that as the outermost select since it's the simplest
      cheap exit.

   The cexp size shrinks from 9 prim sites to 7, and the only
   equality on a non-base type is replaced by an int equality. *)
module Plugin.Test.Bug.MasterModes.V2b.Ideal

open Pipit.Source
open Plugin.Test.Bug.MasterModes.Types

module PXB  = Pipit.Exp.Base
module PPT  = Pipit.Prim.Table
module PPS  = Pipit.Prim.Shallow
module PSSB = Pipit.Prim.HasStream
module PRP  = PipitRuntime.Prim

#set-options "--warn_error -242"

let sh_bool = PSSB.shallow bool
let sh_mode = PSSB.shallow mode
let sh_es   = PSSB.shallow error_severity
let sh_mm   = PSSB.shallow master_mode
let sh_omi  = PSSB.shallow (option master_index_int)
let sh_mi   = PSSB.shallow master_index_int

(* outer ctx (what the lifter exposes to callers): [ref_msg; error; mode_] *)
let ctx_outer : list PPS.shallow_type = [sh_omi; sh_es; sh_mode]

(* After [XLet bool (is_some)] the ctx becomes [bool; ref_msg; error; mode_].
   Inside [XMu] we add master_mode at index 0, then inside the inner XLet
   for pre_master we add another master_mode.

   Final inner ctx at the body level:
     [mm; mm; bool; omi; es; mode]
   index 0 = pre_master, 1 = master_mode_, 2 = is_some,
   index 3 = ref_msg,   4 = error,         5 = mode_                       *)
let ctx_inner : list PPS.shallow_type =
  sh_mm :: sh_mm :: sh_bool :: ctx_outer

unfold let eo_mm = PXB.exp PPS.table ctx_outer sh_mm
unfold let ei_mm = PXB.exp PPS.table ctx_inner sh_mm
unfold let ei_b  = PXB.exp PPS.table ctx_inner sh_bool

unfold let vval (#t: eqtype) {| s: PSSB.has_stream t |} (v: t)
  : PXB.exp PPS.table ctx_inner (PSSB.shallow t)
  = PXB.XBase (PXB.XVal v)

unfold let bvar (n: nat { n < List.Tot.length ctx_inner })
  : PXB.exp PPS.table ctx_inner (List.Tot.index ctx_inner n)
  = PXB.XBase (PXB.XBVar n)

unfold let prm (p: PPS.prim)
  : PXB.exp_apps PPS.table ctx_inner p.prim_ty
  = PXB.XPrim #PPS.table #ctx_inner p

(* runtime helper: total Some?.v with default *)
let some_v_or_default (o: option master_index_int): master_index_int =
  match o with
  | Some v -> v
  | None   -> 0

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

unfold let eq_mi : PPS.prim = {
  prim_id  = Some "Prims.op_Equality";
  prim_ty  = PPT.FTFun sh_mi (PPT.FTFun sh_mi (PPT.FTVal sh_bool));
  prim_sem = op_Equality;
}

unfold let is_some_p : PPS.prim = {
  prim_id  = Some "FStar.Pervasives.Native.uu___is_Some";
  prim_ty  = PPT.FTFun sh_omi (PPT.FTVal sh_bool);
  prim_sem = Some?;
}

unfold let some_v_p : PPS.prim = {
  prim_id  = Some "Plugin.Test.Bug.MasterModes.V2b.Ideal.some_v_or_default";
  prim_ty  = PPT.FTFun sh_omi (PPT.FTVal sh_mi);
  prim_sem = some_v_or_default;
}

let mm_v2b_ideal_core (cfg: config_int): eo_mm =
  let master_enable = cfg.master_enable in
  let master_idx    = cfg.master_idx    in

  // cond_off : mode_ = Mode_Configure || error = S3_Severe
  let cond_off : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (prm bb)
      (PXB.XApps (PXB.XApp (PXB.XApp (prm eq_mode) (bvar 5)) (vval Mode_Configure))))
      (PXB.XApps (PXB.XApp (PXB.XApp (prm eq_es) (bvar 4)) (vval S3_Severe))))
  in
  // cond_pre0 : pre_master = Master_Off
  let cond_pre0 : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (prm eq_mm) (bvar 0)) (vval Master_Off))
  in
  // cond_follower : is_some && not master_enable  (uses bvar 2, the CSE'd is_some)
  let cond_follower : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (prm aa)
      (bvar 2))
      (vval (op_Negation master_enable)))
  in
  // cond_main : is_some && master_enable && error <> S2_Error
  let cond_main : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (prm aa)
      (PXB.XApps (PXB.XApp (PXB.XApp (prm aa)
        (bvar 2))
        (vval master_enable))))
      (PXB.XApps (PXB.XApp (PXB.XApp (prm neq_es) (bvar 4)) (vval S2_Error))))
  in
  // cond_eq_some : Some?.v ref_msg = master_idx   (eq on int, not option)
  let cond_eq_some : ei_b =
    PXB.XApps (PXB.XApp (PXB.XApp (prm eq_mi)
      (PXB.XApps (PXB.XApp (prm some_v_p) (bvar 3))))
      (vval master_idx))
  in

  // body_eq_some : if cond_eq_some then Current_Master else Backup_Master
  let body_eq_some : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (prm sel_mm)
      cond_eq_some) (vval Current_Master)) (vval Backup_Master))
  in
  // body_main : if cond_main then body_eq_some else Master_Off
  let body_main : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (prm sel_mm)
      cond_main) body_eq_some) (vval Master_Off))
  in
  // body_pre0_then : if cond_follower then Follower else body_main
  let body_pre0_then : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (prm sel_mm)
      cond_follower) (vval Follower)) body_main)
  in
  // body_pre0 : if cond_pre0 then body_pre0_then else pre_master
  let body_pre0 : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (prm sel_mm)
      cond_pre0) body_pre0_then) (bvar 0))
  in
  // body_inner : if cond_off then Master_Off else body_pre0
  let body_inner : ei_mm =
    PXB.XApps (PXB.XApp (PXB.XApp (PXB.XApp (prm sel_mm)
      cond_off) (vval Master_Off)) body_pre0)
  in

  // inner XLet binds pre_master = Master_Off `fby` master_mode_
  let mu_body : PXB.exp PPS.table (sh_mm :: sh_bool :: ctx_outer) sh_mm =
    PXB.XLet sh_mm
      (PXB.XFby Master_Off (PXB.XBase (PXB.XBVar 0)))
      body_inner
  in
  // XMu binds master_mode_
  let mu_term : PXB.exp PPS.table (sh_bool :: ctx_outer) sh_mm =
    PXB.XLet sh_mm (PXB.XMu mu_body) (PXB.XBase (PXB.XBVar 0))
  in
  // outermost XLet binds is_some = Some? ref_msg
  PXB.XLet sh_bool
    (PXB.XApps #_ #ctx_outer (PXB.XApp
      (PXB.XPrim #PPS.table #ctx_outer
        ({ prim_id  = Some "FStar.Pervasives.Native.uu___is_Some";
           prim_ty  = PPT.FTFun sh_omi (PPT.FTVal sh_bool);
           prim_sem = Some?; }))
      (PXB.XBase (PXB.XBVar 0))))
    mu_term
