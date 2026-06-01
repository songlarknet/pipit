(** State machines (mode, sync, master, ref-trigger-offset, ref-message, cycle-time)

   NOTE: NONE of the streaming state machines in this module have been
   ported to the new pipeline yet. Major blockers:
     1. Multi-arm pattern matching over stream scrutinees (pre_sync,
        pre_master) is unsupported — the new lifter only supports
        static-scrutinee `match` for `AppPureConst` (see
        [Pipit.Source.Ast.Lower] "AMatch on stream scrutinee is not
        yet supported").
     2. `cfg: config` parameters trigger
        `has_stream config` typeclass resolution failures because the
        lifter treats helper calls such as
        [config_master_enable cfg] as APrim and demands has_stream
        for every arg type.
     3. Cross-module helpers (`S32R.inc_sat`, `S32R.dec_sat`,
        `Util.rising_edge`, `Clocked.current_or_else`,
        `Clocked.get_or_else`, `Clocked.get_clock`,
        `Clocked.get_value`) need to either live in a `#lang-pipit`
        module or carry an explicit `source_mode` attribute so
        ACallStream picks them up. Most do not.
     4. `let open U64`/`let open S32R` is not supported inside
        `#lang-pipit`; every operator would need an explicit
        qualified-or-FQN call.
*)
module Network.TTCan.Impl.States

module Clocked = Network.TTCan.Prim.Clocked
module S32R    = Network.TTCan.Prim.S32R
module U64     = Network.TTCan.Prim.U64
module Util    = Network.TTCan.Impl.Util

open Network.TTCan.Types
