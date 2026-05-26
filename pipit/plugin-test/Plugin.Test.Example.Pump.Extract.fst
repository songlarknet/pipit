module Plugin.Test.Example.Pump.Extract

(* Extraction of [Plugin.Test.Example.Pump.Check.controller] to a Pulse
  [reset]/[step] pair via the [Pipit.Plugin.Extract.extract] splice.

  [controller] is the pair-input wrapper around [controller_body]; the
  splice currently only supports single-stream-argument functions, so
  the two boolean inputs (estop, level_low) are passed as a pair. *)

open Plugin.Test.Example.Pump.Check

%splice []
  (Pipit.Plugin.Extract.extract (`%controller))
