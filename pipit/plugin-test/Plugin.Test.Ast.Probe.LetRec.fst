(* Targeted experiments: how usable is F*'s built-in `let rec` for
   stream definitions?

   Two open questions:
     (a) parser — does `let rec x : a = non_lambda_expr in body`
         parse at all when `x` is not a function?
     (b) tactic view — when a `Tv_Let true` is produced, can a tactic
         inspect it? Does mutual `let rec ... and ...` show up as a
         single Tv_Let or get desugared away?

   We probe by writing each candidate shape and using a splice tactic
   that just prints what `T.inspect` returns. Uncomment cases that
   fail to parse to record results. *)
module Plugin.Test.Ast.Probe.LetRec

open Pipit.Source

module T   = FStar.Tactics.V2
module Ref = FStar.Reflection.V2
module L   = FStar.List.Tot
module PTB = Pipit.Tactics.Base

(* ---- helper: print the inspected shape of a top-level binding. ---- *)

let probe (nm: string): T.Tac unit =
  let tac_env = T.top_env () in
  let m = T.cur_module () in
  let nm_m = Ref.implode_qn L.(m @ [nm]) in
  let nm_exp = Ref.explode_qn nm_m in
  let lb = PTB.lookup_lb_top tac_env nm_exp in
  T.print ("probe " ^ nm ^ " :: lb.lb_typ = " ^ T.term_to_string lb.lb_typ);
  T.print ("probe " ^ nm ^ " :: lb.lb_def = " ^ T.term_to_string lb.lb_def);
  (* Walk past leading lambdas, then inspect the body. *)
  let (_bs, body) = T.collect_abs lb.lb_def in
  let v = T.inspect body in
  let tag = match v with
    | T.Tv_Var _ -> "Tv_Var"
    | T.Tv_BVar _ -> "Tv_BVar"
    | T.Tv_FVar _ -> "Tv_FVar"
    | T.Tv_UInst _ _ -> "Tv_UInst"
    | T.Tv_App _ _ -> "Tv_App"
    | T.Tv_Abs _ _ -> "Tv_Abs"
    | T.Tv_Arrow _ _ -> "Tv_Arrow"
    | T.Tv_Type _ -> "Tv_Type"
    | T.Tv_Refine _ _ -> "Tv_Refine"
    | T.Tv_Const _ -> "Tv_Const"
    | T.Tv_Uvar _ _ -> "Tv_Uvar"
    | T.Tv_Let true _ _ _ _ -> "Tv_Let TRUE (recursive)"
    | T.Tv_Let false _ _ _ _ -> "Tv_Let false"
    | T.Tv_Match _ _ _ -> "Tv_Match"
    | T.Tv_AscribedT _ _ _ _ -> "Tv_AscribedT"
    | T.Tv_AscribedC _ _ _ _ -> "Tv_AscribedC"
    | T.Tv_Unknown -> "Tv_Unknown"
    | T.Tv_Unsupp -> "Tv_Unsupp"
  in
  T.print ("probe " ^ nm ^ " :: body tag = " ^ tag);
  (* If it's a recursive Tv_Let, print its components. *)
  (match v with
   | T.Tv_Let true attrs b def body2 ->
     T.print ("  rec binder: name = " ^ T.unseal b.ppname
              ^ "  sort = " ^ T.term_to_string b.sort);
     T.print ("  rec def    = " ^ T.term_to_string def);
     T.print ("  rec body   = " ^ T.term_to_string body2)
   | _ -> ());
  ()

let probe_tac (nm: string): T.Tac (list T.sigelt) =
  probe nm;
  []

(* =========================================================
   CASE A — single non-function `let rec` with stream type.
   Existing legacy plugin requires `rec'`; can the parser
   even accept this?
   ========================================================= *)

(* Wrap in a function so that there's a top-level binding to probe. *)
[@@source_mode (ModeFun Stream true Stream)]
let case_a_via_rec' (x: int) =
  let count = rec' (fun count -> 0 `fby` count + 1) in
  count

%splice[] (probe_tac "case_a_via_rec'")

(* The interesting case: can we write the user-facing letrec directly? *)

(* Variant 1: non-function letrec — F* rejects.

   Error 163: "Only function literals with arrow types can be defined
   recursively."

[@@source_mode (ModeFun Stream true Stream)]
let case_a_direct_letrec (x: int) =
  let rec count : int = 0 `fby` count + 1 in
  count

%splice[] (probe_tac "case_a_direct_letrec")
*)

(* Variant 2: wrap as a thunk `unit -> int` to dodge the parser
   restriction. *)

[@@source_mode (ModeFun Stream true Stream)]
let case_a_thunk_letrec (x: int) =
  let rec count (u: unit) : Dv int = 0 `fby` count () + 1 in
  count ()

%splice[] (probe_tac "case_a_thunk_letrec")

(* =========================================================
   CASE B — mutual `let rec ... and ...`.
   Q: does it show up as a single Tv_Let or split?
   ========================================================= *)

(* Uncomment to test:

[@@source_mode (ModeFun Stream true Stream)]
let case_b_mutual (x: int) =
  let rec a : int = 0 `fby` b + 1
  and     b : int = 1 `fby` a in
  a + b

%splice[] (probe_tac "case_b_mutual")
*)

[@@source_mode (ModeFun Stream true Stream)]
let case_b_mutual_thunked (x: int) =
  let rec a (u: unit) : Dv int = 0 `fby` b () + 1
  and     b (u: unit) : Dv int = 1 `fby` a () in
  a () + b ()

%splice[] (probe_tac "case_b_mutual_thunked")

(* =========================================================
   CASE C — let-rec whose binding IS a lambda (legal letrec
   in vanilla F-star). Sanity check for what tactics see in
   the normal case.
   ========================================================= *)

let rec case_c_fn (n: nat) : nat =
  if n = 0 then 0 else case_c_fn (n - 1) + 1

%splice[] (probe_tac "case_c_fn")
