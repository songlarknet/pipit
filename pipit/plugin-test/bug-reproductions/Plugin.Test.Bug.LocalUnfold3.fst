module Plugin.Test.Bug.LocalUnfold3

(* Test whether REFLECTION-CONSTRUCTED `Tv_Let` reduces the same way
   surface `let` does. Hypothesis: surface lets get inlined / zeta'd
   by the elaborator BEFORE typechecking the body, so the reducer
   never sees the let. Reflection lets remain as raw `Tv_Let` nodes
   and the type-position reducer treats their bound `Tv_Var` as
   opaque. *)

module T = FStar.Tactics.V2

let rec get_index (#a: Type) (xs: list a) (i: nat { i < FStar.List.Tot.length xs }): a =
  match xs, i with
  | x :: _,  0 -> x
  | _ :: tl, _ -> get_index tl (i - 1)

let bound_at (xs: list int) (i: nat { i < FStar.List.Tot.length xs }) (v: int { v == get_index xs i }): int = v

(* === Reflection: build [let c3 = 30 :: (let c2 = 20 :: (let c1 = 10 :: [99] in c1) in c2) in bound_at c3 3 99]
   purely via Tv_Let. *)
let _splice_reflection_let (): T.Tac T.term =
  let int_ty : T.term = `int in
  let list_int : T.term = `(list int) in
  let mk_let (name: string) (def: T.term) (body: T.term): T.Tac T.term =
    let nv : T.namedv = { uniq = T.fresh (); sort = T.seal list_int; ppname = T.as_ppname name } in
    let sb : T.simple_binder = {
      ppname = T.as_ppname name;
      uniq   = nv.uniq;
      sort   = list_int;
      qual   = T.Q_Explicit;
      attrs  = [];
    } in
    let body' = T.subst_term [T.DT 0 (T.pack (T.Tv_Var nv))] body in
    T.pack (T.Tv_Let false [] sb def body')
  in
  let c0_def: T.term = `([99] <: list int) in
  let c1_def_open: T.term = T.pack (T.Tv_App (`(Cons #int 10)) (T.pack (T.Tv_BVar (T.pack_bv ({ sort = T.seal list_int; ppname = T.as_ppname "c0"; index = 0 }))), T.Q_Explicit)) in
  let c2_def_open: T.term = T.pack (T.Tv_App (`(Cons #int 20)) (T.pack (T.Tv_BVar (T.pack_bv ({ sort = T.seal list_int; ppname = T.as_ppname "c1"; index = 0 }))), T.Q_Explicit)) in
  let c3_def_open: T.term = T.pack (T.Tv_App (`(Cons #int 30)) (T.pack (T.Tv_BVar (T.pack_bv ({ sort = T.seal list_int; ppname = T.as_ppname "c2"; index = 0 }))), T.Q_Explicit)) in
  let body_open: T.term =
    let v_99 : T.term = `(99 <: int) in
    let i_3  : T.term = `(3 <: nat) in
    let xs_var : T.term = T.pack (T.Tv_BVar (T.pack_bv ({ sort = T.seal list_int; ppname = T.as_ppname "c3"; index = 0 }))) in
    let head = `bound_at in
    T.pack (T.Tv_App (T.pack (T.Tv_App (T.pack (T.Tv_App head (xs_var, T.Q_Explicit))) (i_3, T.Q_Explicit))) (v_99, T.Q_Explicit))
  in
  let tm3 = mk_let "c3" c3_def_open body_open in
  let tm2 = mk_let "c2" c2_def_open tm3 in
  let tm1 = mk_let "c1" c1_def_open tm2 in
  let tm0 = mk_let "c0" c0_def tm1 in
  tm0

let test_reflection: int =
  _ by (let tm = _splice_reflection_let () in T.exact tm)
