(** Message status counters and receive-pending bits *)
module Network.TTCan.Impl.MessageStatus

module S     = Pipit.Sugar.Shallow

module BV64I = Network.TTCan.Prim.BV64.Index
module MSC64 = Network.TTCan.Prim.MSC64

module U64   = Network.TTCan.Prim.U64
module S32R  = Network.TTCan.Prim.S32R
module Clocked= Network.TTCan.Prim.Clocked
module Util  = Network.TTCan.Impl.Util

open Network.TTCan.Types

module SugarBase = Pipit.Sugar.Base
module SugarTac  = Pipit.Sugar.Shallow.Tactics

module UInt8 = FStar.UInt8
module UInt64= FStar.UInt64
module Cast  = FStar.Int.Cast

type status_update = Clocked.t bool
let increment: status_update = Clocked.some' true
let decrement: status_update = Clocked.some' false
let nothing:   status_update = Clocked.none'

let message_status_counters
  (message_id: S.stream app_message_index)
  (update: S.stream (Clocked.t bool))
    : S.stream message_status_counter =
  let open S in
  let^ array = rec' (fun array ->
    let^ pre_array = MSC64.zero `fby` array in
    Clocked.fold pre_array (fun inc ->
      let^ msc = MSC64.index array message_id in
      let^ msc = if_then_else inc (S32R.inc_sat msc) (S32R.dec_sat msc) in
      MSC64.update array message_id msc) update) in
  MSC64.index array message_id

let rx_pendings
  (chk: S.stream (Clocked.t app_message_index))
  (rx:  S.stream (Clocked.t app_message_index))
    : S.stream bool =
  let open S in
  let^ array = rec' (fun array ->
    let^ pre_array = BV64I.zero `fby` array in
    // first clear rx from previous check
    let^ clear_check = Clocked.fold array (fun chk_ix ->
        BV64I.clear array (S32R.extend chk_ix)
      ) (Clocked.none' `fby` chk) in
    // next update with newest receive
    let^ rx_array = Clocked.fold array (fun rx_ix ->
        BV64I.set clear_check (S32R.extend rx_ix)
      ) rx in
    rx_array
  ) in
  Clocked.fold (const true)
    (fun chk_ix -> BV64I.index array (S32R.extend chk_ix)) chk
