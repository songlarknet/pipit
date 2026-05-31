module Example.Pump.Extract

(* Extraction of Pump.Check stream functions to Pulse [reset]/[step] pairs
  via the [Pipit.Plugin.Extract.extract] splice.

  [controller_body] is the two-stream-input form taking [estop] and
  [level_low] as separate arguments. [controller] is the pair-input
  wrapper around it. *)

open Example.Pump.Check

%splice[]
  (Pipit.Plugin.Extract.extract (`%controller_body))

%splice[]
  (Pipit.Plugin.Extract.extract (`%controller))
