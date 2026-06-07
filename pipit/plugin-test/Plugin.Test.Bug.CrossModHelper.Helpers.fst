(* Plain F* helpers (NOT `#lang-pipit`, NO [@@source_mode] attrs)
   exercised from `Plugin.Test.Bug.CrossModHelper`. See that module's
   header comment for the README workaround 3 context. *)
module Plugin.Test.Bug.CrossModHelper.Helpers

let opt_get_or_else (dflt: int) (clck: option int): int =
  match clck with
  | Some v -> v
  | None -> dflt

let add_then_clamp (a: int) (max: int): int =
  let s = a + 1 in
  if s > max then max else s
