module ThermDriver.Check

open Pipit.Exp.Base

open Pipit.System.Base
open Pipit.System.Ind
open Pipit.System.Exp

module T = Pipit.Tactics
module Sugar = Pipit.Sugar

module PPV = Pipit.Prim.Vanilla

type temperatures = Sugar.ints

(*
 type TCMD = enum { NONE, RESET, READ, SET_INT_ENABLE, SET_INT_DISABLE };
*)
type tcmds = Sugar.ints

let cmd_none':            int = 0
let cmd_reset':           int = 1
let cmd_read':            int = 2
let cmd_set_int_enable':  int = 3
let cmd_set_int_disable': int = 4

let cmd_none:            tcmds = Sugar.pure cmd_none'
let cmd_reset:           tcmds = Sugar.pure cmd_reset'
let cmd_read:            tcmds = Sugar.pure cmd_read'
let cmd_set_int_enable:  tcmds = Sugar.pure cmd_set_int_enable'
let cmd_set_int_disable: tcmds = Sugar.pure cmd_set_int_disable'

(*
type TRSP = struct {
  cmd_ok:    bool;
  temp:      TEMPERATURE; -- when cmd_ok
  fresh:     bool;        -- when cmd_ok
};
*)
let trsp' = PPV.TPair PPV.TBool (PPV.TPair PPV.TInt PPV.TBool)
type trsp  = (bool & (int & bool))
type trsps = Sugar.s trsp'

let mk_trsp
  (cmd_ok: Sugar.bools)
  (temp:   temperatures)
  (fresh:  Sugar.bools)
         : trsps =
  Sugar.tup cmd_ok (Sugar.tup temp fresh)

let cmd_ok (t: trsps): Sugar.bools  = Sugar.fst t
let temp   (t: trsps): temperatures = Sugar.fst (Sugar.snd t)
let fresh  (t: trsps): Sugar.bools  = Sugar.snd (Sugar.snd t)

let thermometer
  (cmd: tcmds)
  (temp: temperatures)
  (havoc: Sugar.bools)
   =
    // Sugar.s (PPV.TPair trsp' PPV.TBool) =
  let open Sugar in
  letrec' (fun ok ->
    if_then_else havoc ff
      (if_then_else (cmd =^ cmd_reset) tt
        (fby true ok)))
    (fun ok ->
  letrec' (fun int_en ->
    if_then_else (cmd =^ cmd_set_int_disable) ff
    (if_then_else (cmd =^ cmd_set_int_enable) tt
      (fby false int_en)))
  (fun int_en ->
  tt
  ))

(*

node thermometer(
  cmd:        TCMD;
  temp:       TEMPERATURE;
  havoc:      bool;
) returns (
  rsp:        TRSP;
  read_clock: bool;
)
var
  ok:         bool;
  int_en:     bool;
  temp_buf:   TEMPERATURE;
  int_high:   bool;
let
  ok =
    if havoc then false
    else if cmd = RESET then true
    else (true -> pre ok);
  int_en =
    if cmd = SET_INT_DISABLE then false
    else if cmd = SET_INT_ENABLE then true
    else (false -> pre int_en);
  read_clock = every2() and ok;
  temp_buf = current_when(temp, read_clock);
  int_high =
    if read_clock and int_en then true
    else if false -> pre (cmd = READ) then false
    else (false -> pre int_high);

  rsp = TRSP {
    cmd_ok    = ok and cmd <> NONE;
    temp      = if ok and cmd = READ then temp_buf else 123456;
    fresh     = int_high;
  };
tel

*)
