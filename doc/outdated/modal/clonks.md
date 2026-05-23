# cut

```
XCut:
  exp ctx  ctx' ->
  exp ctx' res  ->
  exp ctx  res

  S   |- arg  =>* Srg
  Srg |- body =>  vody
--------------------------------------
S |- XCut arg body => vody
```

# reset

```
XReset:
  exp ctx  bool ->
  exp ctx  ctx' ->
  exp ctx' a   ->
  exp ctx  a



reset_slice S rst = S'
  S   |- arg  =>* Srg
  Srg |- body =>  vody
--------------------------------------
S |- XReset rst arg body => vody


s |- arg => vrg    vrg |- body => vody
--------------------------------------
s |- XReset rst arg body => vody



s, S |- rst => true  s, S |- arg => vrg    arg |- body => vody
--------------------------------------
s, S |- XReset rst arg body => vody

s, S |- rst => false  s, S |- arg => vrg    arg |- body => vody
--------------------------------------
s, S |- XReset rst arg body => vody


reset_slice S rst: S
reset_slice s _ rst = s
reset_slice s,S rst =
  if s,S |- rst => true
  then s
  else s,reset_slice S rst
```

# merge / match

```
XMerge1:
  exp ctx (option a) ->
  exp   a  res ->
           res ->
  exp ctx  res


  S |- cond =>* Sond
  take_options Sond = S'
  S' |- body => vody
-----------------------------
S |- XMerge1 cond body => vody



XMerge2:
  exp ctx (either a b) ->
  exp   a  res ->
  exp   b  res ->
  exp ctx  res


XMergeBool:
  k: clock ctx ->
  exp (ctx;k) a ->
  exp (ctx;not k) b ->
  exp   a  res ->
  exp   b  res ->
  exp ctx  res

```


# rules

```
XReset rst arg ?i = arg.i
XReset rst arg (f x y) = f (XReset rst arg x) (XReset rst arg y)
XReset rst arg (let x = e in e') =
  let x = (XReset rst arg e) in
  XReset rst (arg,x) e'

XReset rst arg (rec x. e) =
  rec x. (XReset rst (arg,x) e)

XReset rst arg (v fby e) =
  if rst then v else (v fby XReset rst arg e)

XReset true arg (v fby e) = v
// XReset false arg e = XCut arg e


XMerge1 scrt ?i dflt = if Some? scrt then scrt.i else dflt
XMerge1 scrt (f x y) dflt = if Some? scrt then f (XMerge1 scrt x undefined) (XMerge1 scrt y undefined) else dflt
XMerge1 scrt (let x = e in e') dflt =
  let x = XMerge1 scrt e undefined in
  XMerge1 (scrt,x) e' dflt
XMerge1 scrt (rec x. e) dflt =
  rec x. XMerge1 (scrt,x) e dflt
XMerge1 scrt (v fby e) dflt =
  let rec x =
    // hmm wrong
    if Some? scrt then v fby e
    else v fby x
  in if Some? scrut then x else dflt

XMerge1 None e dflt = dflt
XMerge1 (Some t) e dflt = XCut t e

```