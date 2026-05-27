module Plugin.Test.Example.Pump.Extract

(* Extraction of Pump.Check stream functions to Pulse [reset]/[step] pairs
  via the [Pipit.Plugin.Extract.extract] splice.

  [controller_body] is the two-stream-input form taking [estop] and
  [level_low] as separate arguments; [controller] is the pair-input
  wrapper that destructures a single [stream (bool & bool)] before
  delegating. Both work directly through the splice. *)

open Plugin.Test.Example.Pump.Check

%splice [
    controller_body_state; __extractable_controller_body;
    controller_body_system; controller_body_reset; controller_body_step
  ]
  (Pipit.Plugin.Extract.extract (`%controller_body))

%splice [
    controller_state; __extractable_controller;
    controller_system; controller_reset; controller_step
  ]
  (Pipit.Plugin.Extract.extract (`%controller))

