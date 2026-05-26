module Plugin.Test.Example.Simple.Extract

(* Extraction of [Plugin.Test.Example.Simple.Check.count_when] to a Pulse
  [reset]/[step] pair, driven by the [Pipit.Plugin.Extract.extract] splice.

  The splice emits four bindings in this module:

    count_when_state   : Type
    count_when_system  : Pipit.Exec.Exp.esystem (bool & unit) count_when_state int
    count_when_reset
    count_when_step

  This file used to contain the hand-written boilerplate; the splice now
  derives it mechanically from the source binding's type. *)

open Plugin.Test.Example.Simple.Check

%splice [count_when_state; __extractable_count_when;
         count_when_system; count_when_reset; count_when_step]
  (Pipit.Plugin.Extract.extract (`%count_when))
