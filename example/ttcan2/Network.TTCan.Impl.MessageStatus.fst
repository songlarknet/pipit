(** Message status counters and receive-pending bits

   NOTE: The two top-level streaming functions [message_status_counters]
   and [rx_pendings] are NOT yet ported. The new pipeline (#lang-pipit
   + lift_ast_tac1) requires cross-module helpers such as [S32R.inc_sat],
   [S32R.dec_sat], [MSC64.index], [MSC64.update], [BV64I.set],
   [BV64I.clear] to carry [source_mode] attributes (or to be defined
   inside [#lang-pipit] modules); none of them do today, so the lifter
   treats them as static APrims and fails when stream-bound variables
   appear in their args. *)
module Network.TTCan.Impl.MessageStatus

module PSSB  = Pipit.Prim.HasStream
module BV64I = Network.TTCan.Prim.BV64.Index
module MSC64 = Network.TTCan.Prim.MSC64

module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked
module Util  = Network.TTCan.Impl.Util

open Network.TTCan.Types

module UInt8 = FStar.UInt8
module UInt64= FStar.UInt64
module Cast  = FStar.Int.Cast

type status_update = Clocked.t bool

let increment: status_update = Some true
let decrement: status_update = Some false
let nothing:   status_update = None
