(* PROTOTYPE: a genuine [mu_strong] separation.

   [counting = µc. count_when true ((0 fby c) = 9)] where
   [count_when true r = µa. (if r then 0 else (0 fby a)) + 1] is a resettable
   counter. The feedback [c] is used as a *reset control*: the inner counter [a]
   has its own register [0 fby a], the reset reads [0 fby c], and they agree only
   via the outer knot [c = a].

   - Weak [mu] must prove the body for an arbitrary [c] with just [0 <= c < 10];
     [c = 5] constant satisfies that yet the reset never fires and [a] runs away,
     so the weak body triple is FALSE -> stuck.
   - [mu_strong] has [c = a], so the reset reads [a]'s own value; [a] cycles in
     [1,9]. Provable with the natural bound.

   Uses a select-style [ite]:  ap (ap (map (\c t e. if c then t else e)) c) t <*> e. *)
module Pipit.Extensional.Example.CountWhen

module E  = Pipit.Extensional.Base
module ES = Pipit.Extensional.Stream
module S  = Pipit.Extensional.System
module L  = Pipit.Extensional.Logic
module SL = Pipit.Extensional.System.Logic
module SB = Pipit.System.Base
module PT = Pipit.Tactics

(* Select-style if-then-else, applicatively. *)
let select3
  (#input #a: Type)
  (c: S.sys input bool)
  (t: S.sys input a)
  (e: S.sys input a)
  : S.sys input a
  =
  S.ap (S.ap (S.map (fun (cc: bool) (tt: a) (ee: a) -> if cc then tt else ee) c) t) e

(* Inner body of [count_when true r], as a mu-body over feedback [a]. Its input
   is [(a, (c, ()))]: [a] the inner feedback, [c] the outer feedback (read for
   the reset). Output: [if (0 fby c) = 9 then 1 else (0 fby a) + 1]. *)
let inner_body : S.sys (int & (int & unit)) int =
  let proj_a : S.sys (int & (int & unit)) int =
    S.map (fun (x: int & (int & unit)) -> fst x) S.id in
  let proj_c : S.sys (int & (int & unit)) int =
    S.map (fun (x: int & (int & unit)) -> fst (snd x)) S.id in
  let reset  : S.sys (int & (int & unit)) bool =
    S.map (fun (v: int) -> v = 9) (S.fby 0 proj_c) in
  let count  : S.sys (int & (int & unit)) int =
    S.map (fun (v: int) -> v + 1) (S.fby 0 proj_a) in
  select3 reset (S.const 1) count

(* [body_c = count_when true ((0 fby c) = 9)] : the inner resettable counter,
   closed over the outer feedback [c]. Input [(c, ())]. *)
let body_c : S.sys (int & unit) int = S.mu inner_body

(* [counting = µc. body_c]. *)
let counting : S.sys unit int = S.mu body_c

(* The target: [0 <= c < 10]. *)
let cp : S.sys unit prop = S.const True
let cq : S.sys (unit & int) prop =
  S.map (fun (io: unit & int) -> b2t (0 <= snd io && snd io < 10)) S.id

(* Attempt 1: whole-system 1-induction with the naked bound. *)
let lemma_counting_bound_try1 (_: unit)
  : Lemma (SL.triple cp counting cq)
  =
  assert (SL.base_case_sys cp counting cq) by (PT.norm_full []);
  assert (SL.step_case_sys cp counting cq) by (PT.norm_full []);
  SL.induct1_sys cp counting cq

(* WEAK-STUCK demonstration. Weak [mu] on the outer µ must prove [body_c]'s
   bound for an arbitrary feedback [c] that only satisfies [0 <= c < 10] --- it
   does NOT get [c = output]. The obligation is: precondition bounds the *input
   feedback*, postcondition bounds the *output*. It is FALSE ([c = 5] constant is
   bounded, yet the inner counter never resets and runs to 10+). We witness the
   falsity directly: run [body_c] on the constant-5 feedback with the inner
   oracle forced (by the inner knot) to the runaway counter [1,2,3,...], and read
   off output 10 at step 9. *)
let feedback5 : E.stream (int & unit) = fun _ -> (5, ())
(* Inner-knot oracle: the guess equals the counter's own output [n+1]. *)
let orc_runaway : E.stream (SB.option_type_sem body_c.oracle) = fun n -> n + 1

let lemma_weak_body_false (_: unit)
  : Lemma (
      let ios = S.with_oracle body_c feedback5 orc_runaway in
      (* feedback is bounded, and the inner knot-assumption holds, yet the
         output at step 9 is 10 --- violating [0 <= out < 10]. *)
      S.stream_of_output body_c.raw ios 9 == 10)
  =
  assert (
    let ios = S.with_oracle body_c feedback5 orc_runaway in
    S.stream_of_output body_c.raw ios 9 == 10) by (PT.norm_full [])
