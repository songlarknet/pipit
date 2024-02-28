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

open Pipit.Sugar.Shallow.Tactics.Lift
module Tac = FStar.Tactics

type status_update = Clocked.t bool

let increment: status_update = Some true
let decrement: status_update = Some false
let nothing:   status_update = None

[@@Tac.preprocess_with preprocess]
let message_status_counters
  (message_id: stream can_buffer_id)
  (update: stream (Clocked.t bool))
    : stream message_status_counter =
  let rec array =
    let pre_array = MSC64.zero `fby` array in
    if Clocked.get_clock update
    then
      let inc = Clocked.get_value update in
      let msc = MSC64.index pre_array message_id in
      let msc = if inc then S32R.inc_sat msc else S32R.dec_sat msc in
      MSC64.update pre_array message_id msc
    else
      pre_array
  in MSC64.index array message_id

%splice[] (autolift_binds [`%message_status_counters])

[@@Tac.preprocess_with preprocess]
let rx_pendings
  (chk: stream (Clocked.t can_buffer_id))
  (rx:  stream (Clocked.t can_buffer_id))
    : stream bool =
  let rec array =
    let pre_array = BV64I.zero `fby` array in
    // first clear rx from previous check
    let pre_chk = None `fby` chk in
    let clear_check =
      if Clocked.get_clock pre_chk
      then BV64I.clear pre_array (Clocked.get_value pre_chk)
      else pre_array
    in
    // next update with newest receive
    let rx_array =
      if Clocked.get_clock rx
      then BV64I.set clear_check (Clocked.get_value rx)
      else clear_check
    in
    rx_array
  in
  if Clocked.get_clock chk
  then BV64I.index array (Clocked.get_value chk)
  else true

%splice[] (autolift_binds [`%rx_pendings])
