module Pipit.Source

open Pipit.Plugin.Interface

assume new type stream : eqtype -> Type

[@@(source_mode (ModeFun Static true (ModeFun Stream true Stream)))]
assume val fby (#a: Type) (x xs: a): a

// [@@(pipit_core_of_source `%fby)]
// private let fby_core (#a: Type): exp a a