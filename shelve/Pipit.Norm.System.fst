module Pipit.Norm.System

open Pipit.Prim.Table

open Pipit.Norm.Context
open Pipit.Norm.Defs
open Pipit.Norm.Exp

module C  = Pipit.Context.Base
module CP = Pipit.Context.Properties

module S = Pipit.System.Base

let xsystem (#t: table) (input state: context t) (ty: t.ty) = S.system (row input) (row state) (t.ty_sem ty)

let system_free
  (ty: Type)
  (t: S.system (ty & 'i) 's 'r)
    : S.system 'i 's 'r =
  {
    init = t.init;
    step = (fun i s s' r ->
      exists (free: ty). t.step (free, i) s s' r);
    chck = t.chck;
  }

let system_let
  (f: 'i -> 'a)
  (t: S.system ('a & 'i) 's 'r)
    : S.system 'i 's 'r =
  {
    init = t.init;
    step = (fun i s s' r -> t.step (f i, i) s s' r);
    chck = t.chck;
  }

let system_fby
  (init:   'a)
  (update: 'r -> 'a)
  (t: S.system ('a & 'i) 's 'r)
    : S.system 'i ('a & 's) 'r =
  {
    init = (fun (sa, s) -> sa == init /\ t.init s);
    step = (fun i (sa, s) (sa', s') r ->
      t.step (sa, i) s s' r /\
      sa' == update r);
    chck = S.map_checks snd t.chck;
  }

let rec translate_defs
  (#t: table) (#nc: ncontext t)
  (n: ndefs t nc):
    Tot (S.system (row nc.available) (row (state_of_ndefs n)) (row (nc_all nc)))
      (decreases n) =
  match n with
  | NDNil -> S.system_input
  | NDCons NDFree rest ->
    let t' = translate_defs rest in
    system_free _ t'
  | NDCons (NDLet e) rest ->
    let t' = translate_defs rest in
    system_let (fun row -> nexp_sem row e) t'
  | NDCons (NDFby v e) rest ->
    let t' = translate_defs rest in
    system_fby v (fun row -> nexp_sem row e) t'

let translate_sys
  (#t: table) (#nc: ncontext t)
  (n: nsys t nc):
    S.system (row nc.available) (row (state_of_ndefs n.defs)) (row (nc_all nc)) =
  let s = translate_defs n.defs in
  let chcks = n.checks in
  // TODO system needs to be able to describe always-implication properties
  s

let translate
  (#t: table) (#nc: ncontext t) (#ty: t.ty)
  (n: norm t nc ty):
    xsystem nc.available (state_of_ndefs n.sys.defs) ty =
  let s = translate_sys n.sys in
  S.system_map (fun row -> nexp_sem row n.exp) s
