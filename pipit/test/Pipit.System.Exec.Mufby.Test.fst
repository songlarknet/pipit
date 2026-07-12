(* Concrete semantics test for the fused single-evaluation mufby loop.

   The fused loop `esystem_mufby seed f g` implements
     res = f(acc);   acc = seed fby g(res)
   applying `f` and `g` exactly once per step (contrast esystem_mu_causal,
   which evaluates its body twice per step to resolve the immediate knot).

   Here we instantiate it as a plain counter:
     f(acc) = acc + 1,   g(res) = res,   seed = 0
   so acc = 0, 1, 2, ...  and  output res = 1, 2, 3, ...
*)
module Pipit.System.Exec.Mufby.Test

open Pipit.System.Base
open Pipit.System.Exec

module List = FStar.List.Tot

(* f: (acc, input) -> acc + 1  (stateless) *)
let tf : esystem (int & unit) None int = esystem_project (fun (acc, _) -> acc + 1)

(* g: (res, input) -> res  (stateless identity: next accumulator = res) *)
let tg : esystem (int & unit) None int = esystem_project (fun (res, _) -> res)

(* The fused counter loop. `esystem_of_exp` wires XMufby to exactly this shape. *)
let counter = esystem_mufby #unit #(int & unit) #(int & unit) #int #int
  0 (fun i v -> (v, i)) (fun i v -> (v, i)) tf tg

(* Run n steps forward in time, collecting outputs in temporal order. *)
let rec run (#st: option Type) (#o: Type)
  (t: esystem unit st o) (s: option_type_sem st) (n: nat)
  : Tot (list o) (decreases n) =
  if n = 0 then []
  else
    let (s', v) = t.step () s in
    v :: run t s' (n - 1)

(* The output stream is 1, 2, 3, 4 -- the correct running counter, with `f`
   and `g` each applied once per step. *)
let _test_counter : unit =
  assert_norm (run counter counter.init 4 == [1; 2; 3; 4])

(* A second check: a running sum of a constant `2` fed through `f`.
     f(acc) = acc + 2,  g(res) = res,  seed = 0   ->  2, 4, 6, 8 *)
let tf2 : esystem (int & unit) None int = esystem_project (fun (acc, _) -> acc + 2)
let sum2 = esystem_mufby #unit #(int & unit) #(int & unit) #int #int
  0 (fun i v -> (v, i)) (fun i v -> (v, i)) tf2 tg

let _test_sum2 : unit =
  assert_norm (run sum2 sum2.init 4 == [2; 4; 6; 8])
