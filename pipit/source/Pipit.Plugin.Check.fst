module Pipit.Plugin.Check

module PPL = Pipit.Plugin.Lift

open Pipit.Plugin.Interface

module Tac = FStar.Tactics.V2
module Ref = FStar.Reflection.V2

module PTB = Pipit.Tactics.Base

module Range = FStar.Range

module List = FStar.List.Tot

module PSSB = Pipit.Sugar.Shallow.Base
module PPS  = Pipit.Prim.Shallow
module PPT  = Pipit.Prim.Table
module PXB  = Pipit.Exp.Base
module PXBi  = Pipit.Exp.Binding

module PTC = Pipit.Tactics.Cse

module TermEq = FStar.Reflection.TermEq.Simple



// let check_tac1 (nm_src nm_core: string) : Tac.Tac (list Tac.sigelt) =
//   let tac_env = Tac.top_env () in
//   let m = Tac.cur_module () in
//   let nm_src_m = Ref.implode_qn List.(m @ [nm_src]) in
//   let nm_core_m = Ref.implode_qn List.(m @ [nm_core]) in
//   let nm_src_m_exp = Ref.explode_qn nm_src_m in
//   let lb_src = PTB.lookup_lb_top tac_env nm_src_m_exp in
//   let se_src = match Ref.lookup_typ tac_env nm_src_m_exp with
//     | None -> Tac.fail "impossible"
//     | Some s -> s in
//   let lb_mode = match mode_of_attrs (Ref.sigelt_attrs se_src) with
//     | None -> Tac.fail "expected source function to have source_mode annotation"
//     | Some m -> m in
//   let e = env_nil [nm_src_m, lb_mode] in
//   let nm_src_const = Tac.pack (Tac.Tv_Const (Ref.C_String nm_src_m)) in
//   let tm = lb_src.lb_def in
//   let _, tm = lift_tm e tm (Some lb_mode) in
//   let tm = Tac.pack (Tac.Tv_Abs (Tac.namedv_to_binder e.ctx_uniq ctx_ty) tm) in
//   let _, se = core_sigelt e [`core_lifted] (Some nm_src_m) (Some nm_core_m) lb_mode tm in
//   let extra_sigelts = List.rev (Tac.read e.extra_sigelts) in
//   List.(extra_sigelts @ [se])

// let lift_tac1 (nm_src: string) : Tac.Tac (list Tac.sigelt) =
//   lift_tac nm_src (env_core_nm nm_src)