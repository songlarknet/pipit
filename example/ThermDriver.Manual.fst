module ThermDriver.Manual

module ST = FStar.HyperStack.ST

module U8  = FStar.UInt8

type addr = U8.t
type reg  = U8.t
type temperature = U8.t

// type either a b = | Inl: a -> either a b | Inr: b -> either a b

type error =
 | NOPE


assume val sleep: unit -> ST.St unit

assume val i2c_write_reg (dst: addr) (rg: reg) (v: U8.t): ST.St (either error unit)

assume val i2c_read_reg (dst: addr) (rg: reg): ST.St (either error U8.t)

assume val temperature_reading (t: temperature): ST.St unit

let thrm_addr: addr = U8.uint_to_t 0x10
let reset_reg: reg  = U8.uint_to_t 0x13
let int_reg: reg    = U8.uint_to_t 0x14
let thrm_reg: reg   = U8.uint_to_t 0x20

let rec
  reset (): ST.St unit =
    match i2c_write_reg thrm_addr reset_reg U8.one with
      | Inl _ -> sleep (); reset ()
      | Inr _ -> init ()
and
  init (): ST.St unit =
    match i2c_write_reg thrm_addr int_reg U8.one with
    | Inl _ -> sleep (); reset ()
    | Inr _ -> read_loop U8.zero
and
  read_loop (failures: U8.t): ST.St unit =
    let open U8 in
    match i2c_read_reg thrm_addr thrm_reg with
    | Inl _ -> if failures <^ U8.uint_to_t 10
               then (sleep (); read_loop (failures +^ U8.one))
               else reset ()
    | Inr t ->
      temperature_reading t; sleep (); read_loop U8.zero


