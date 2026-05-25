# F* pop-up seminar: Pipit

## Background
My background is in streaming programming languages and stream fusion.
For the past three or four years I was working at a self-driving car startup.
There are multiple levels of criticality on a self-driving car.
The driving decisions are obviously important, but the microcontrollers that carry out those driving decisions are even more important.
So, I spent a lot of time verifying the low-level code that interfaced with the microcontrollers.

I've just started a postdoc at ANU.

## A case study: anti-lock braking system

Anti-lock brakes for a motorcycle.

Diagram of a motorcycle: wheels `\omega_F` and `\omega_R` for wheel speeds.
Assume that we also have an accelerometer.

We need to estimate the vehicle's speed.

```fstar
let veh_speed_estimator \omega_F \omega_R a_z =
  
```


## notes

Properties:

if `\omega_F ~ \omega_R` then accuracy ok

if `\omega_F ~ \omega_R` within last minute, then estimated range is not too bad

Lustre!

```
let veh_speed_estimate (i: Sugar.s inputs): Sugar.s estimate =
  let open Sugar in
  let wheel_front = (fun i -> i.wheel_front) <$> i    in
  let wheel_rear  = (fun i -> i.wheel_rear)  <$> i    in
  let accel_z     = (fun i -> i.accel_z)     <$> i    in
  let wheel_circ  = pure wheel_circ                in
  let z1000       = pure 1000                      in
  let accelerometer_tolerance = pure accelerometer_tolerance in
  let mk_estimate lo hi = (fun lo hi -> { speed_lo = lo; speed_hi = hi }) <$> lo <*> hi in

  let front = (wheel_front *^ wheel_circ) /^ z1000 in
  let rear  = (wheel_rear  *^ wheel_circ) /^ z1000 in
  let min_vel = min <$> front <*> rear             in
  let max_vel = max <$> front <*> rear             in

  let ok    = within_tolerance <$> wheel_front <*> wheel_rear <*> pure wheel_tolerance in

  let lo = rec' (fun lo ->
    if_then_else ok min_vel ((min_vel --> pre lo) +^ accel_z -^ accelerometer_tolerance)) in
  let hi = rec' (fun hi ->
    if_then_else ok max_vel ((max_vel --> pre hi) +^ accel_z +^ accelerometer_tolerance)) in

  let est = mk_estimate lo hi in

  check' "veh_speed_estimate_accurate"
    ((within_tolerance <$> wheel_front <*> wheel_rear <*> pure wheel_tolerance) =>
     (within_tolerance <$> lo <*> hi <*> pure wheel_tolerance_speed)) (
  est)
```

```
\dia_n(\omega_F ~ \omega_R) \rightarrow lo ~ hi
```

```
\dia(\omega_F ~ \omega_R) \rightarrow lo ~_{tol \cdot ticks_ago} hi
```

```
e := v | e e | x | fby v e | e -> e |
   | \mu x. e[x]
   | let x = e in e[x]
   | check string e in e
```

```
\Sigma := \sigma | \Sigma; \sigma
\sigma := { \ov{x = v} }
```

judgment form
```
\Sigma \vdash e \rightarrow v
```

```

Sigma |- v ==> v
(Val)

Sigma; sigma |- v ==> sigma(x)
(Var)

Sigma |- e ==> \hat{f}    Sigma |- e' ==> v
-------------------------------------------
        Sigma |- e e' ==> \hat{f} v
(App)

sigma |- fby v e ==> v
(Fby1)

Sigma        |-       e ==> v'
------------------------------
Sigma; sigma |- fby v e ==> v'
(FbyS)

sigma |- e       ==> v
----------------------
sigma |- e -> e' ==> v
(Then1)

Sigma; sigma |-      e' ==> v'
----------------------
Sigma; sigma |- e -> e' ==> v'
(ThenS)


Sigma |- e[x := \mu x. e[x]] ==> v
----------------------------------
Sigma |-        \mu x. e[x]  ==> v
(Mu)

Sigma |-         e'[x := e] ==> v
---------------------------------
Sigma |- let x = e in e'[x] ==> v
(Let)

Sigma |- e ==> true     Sigma |- e' ==> v
-----------------------------------------
    Sigma |- check name e in e' ==> v
(Check)
```

diagram:
```
                         runs on real hardware!
sugar --> exp --> low* --> c
           |
           | (mostly verified)
           v
    transition system
        k-inductive proofs!
```


## Questions for the F* community

* any plan or interest in extending effect system to handle non-monadic effects? (eg arrow style)
* implicit conversions, eg `int -> exp int`

## Future work

* clocks, letrecs, contracts
* common subexpression elimination (very important for proving properties involving stateful predicates)
* finish / resurrect proof of lts
* start proof of compilation
* case studies: antilock braking system? climbing robots?
