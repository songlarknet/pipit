(** Main TTCan controller.

   NOT yet ported. This module is the most heavily streaming code in
   TTCan and combines essentially every feature flagged as
   unsupported by the experiment:
     - static [cfg: config] parameters everywhere
     - cross-module calls into [Network.TTCan.Impl.States],
       [Network.TTCan.Impl.Triggers], [Network.TTCan.Prim.Clocked]
       (current_or_else / map / get_or_else / get_clock / get_value),
       [Network.TTCan.Impl.MessageStatus]
     - multi-arm matches over stream scrutinees
     - [pre #T] explicit type-arg uses
     - [Clocked.map] with anonymous lambdas
     - record projections (Mkref_message?.cycle_index) as first-class
       function values
     - [let open U64] / [let open S32R]
   The base types and stream instances would all need new wrappers
   for the new pipeline; until [Impl.States], [Impl.Triggers],
   [Impl.MessageStatus] are themselves ported, Controller has nothing
   to call. *)
module Network.TTCan.Impl.Controller
