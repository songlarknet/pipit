(* Pure (non-streaming) terms: variables, embedded ground values, and saturated
   applications of a built-in `prim`. Keeping a pure layer distinct from the
   stream layer is the stratification: a `PVar` is *knowably* non-streaming, and
   constant-folding / value computation can run here without touching the
   temporal formers. Design notes and rationale: see Pipit.Exp.Pure.md. *)
module Pipit.Exp.Pure

module PR = Pipit.Exp.Prim

[@@plugin]
type pterm =
  | PVar   : string    -> pterm
  | PValue : PR.value  -> pterm
  | PApp   : PR.prim -> list pterm -> pterm

(* Type inference for pure terms: a free `PVar` is untyped here (no static
   environment yet), a value is typed by `value_ty`, and an application defers
   to `prim_ty` over its recursively inferred argument types. *)
let rec infer_p (e: pterm): Tot (option PR.typ) (decreases e) =
  match e with
  | PVar _      -> None
  | PValue v    -> Some (PR.value_ty v)
  | PApp p args -> (match infer_args args with
                   | Some tys -> PR.prim_ty p tys
                   | None     -> None)
and infer_args (args: list pterm): Tot (option (list PR.typ)) (decreases args) =
  match args with
  | []      -> Some []
  | a :: tl -> (match infer_p a, infer_args tl with
               | Some t, Some ts -> Some (t :: ts)
               | _, _            -> None)
