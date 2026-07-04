(* Synthetic dependency surface for the [MasterModes.V*] bisection
   examples. Mirrors the small slice of [Network.TTCan.Types.{Base,
   Instance}] that [States.master_modes] actually consumes:

     - 3 enum scrutinees with [has_stream] instances,
     - a [has_stream] instance over [option],
     - both a plain-[int] [master_index_int] and a refined-[int]
       [master_index_sr] so we can compare equality costs.
*)
module Plugin.Test.Bug.MasterModes.Types

open Pipit.Source
module PSSB = Pipit.Prim.HasStream

type mode = | Mode_Configure | Mode_Running
%splice[has_stream_mode]
  (derive_has_stream_with_default "mode" "Mode_Configure")

type error_severity = | S0_No_Error | S1_Warning | S2_Error | S3_Severe
%splice[has_stream_error_severity]
  (derive_has_stream_with_default "error_severity" "S0_No_Error")

type master_mode = | Master_Off | Follower | Current_Master | Backup_Master
%splice[has_stream_master_mode]
  (derive_has_stream_with_default "master_mode" "Master_Off")

(* [option] has_stream, copied from [Plugin.Test.Core.Basic]. *)
instance has_stream_option (#a: eqtype) {| PSSB.has_stream a |}: PSSB.has_stream (option a) = {
  ty_id       = `%Pervasives.Native.option :: PSSB.ty_id #a;
  val_default = None;
}

(* Two flavours of [master_index]: plain int vs refined int. *)
type master_index_int = int
type master_index_sr  = i: int { 0 <= i /\ i <= 7 }

(* Refined-int [has_stream] instance: same shape as
   [Pipit.Prim.HasStream.has_stream_int] but tagged with our type name. *)
instance has_stream_master_index_sr: PSSB.has_stream master_index_sr = {
  ty_id       = [`%master_index_sr];
  val_default = 0;
}

(* Static config carriers (no [stream]) \u2014 mirrors how
   [States.master_modes] decomposes [cfg] into static values before the
   [rec]. *)
type config_int = { master_enable: bool; master_idx: master_index_int }
type config_sr  = { master_enable: bool; master_idx: master_index_sr  }
