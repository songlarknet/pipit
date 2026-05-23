# Grammar
```
e :=
  | x | v | v fby e | rec x. e
  | λ x. e | e e'

τ := int | bool    (base streams)
  | τ → τ'         (functions)
  | τ * τ'         (tuples)
  | ● τ            (previous)
```

# Static semantics
```
Γ := Γ, x: τ
   | .
```

∈ Γ'

```
τ stable:

--
int stable

--
bool stable

τ₁ stable
τ₂ stable
--
τ₁ * τ₂ stable
```

```
◯: Γ → Γ

◯ (Γ, x: ●τ)
  | τ stable
  = ◯ Γ, x: τ
  | otherwise
  = ◯ Γ
◯ (Γ, x: τ)
  | τ stable
  = ◯ Γ, x: τ
  | otherwise
  = ◯ Γ
◯ . = .
```

```
Γ ⊢ e : τ:

--
Γ₁, x: τ, Γ₂ ⊢ x: τ


    ⊢ v: τ
◯ Γ ⊢ e: τ
--
Γ ⊢ v fby e: τ

Γ, x: ● τ ⊢ e: τ
--
Γ ⊢ rec x. e: τ

Γ, x: τ₁ ⊢ e: τ₂
--
Γ ⊢ λ x. e: τ₁ → τ₂

Γ ⊢ e:  τ₁ → τ₂
Γ ⊢ e': τ₁
--
Γ ⊢ e e': τ₂
```

# Dynamic semantics
```
Σ ⊢ e => v

------------------
[σ] ⊢ v fby e => v

     Σ ⊢ e => v'
---------------------
σ :: Σ ⊢ v fby e => v'


Σ ⊢ e => (λ x. e)
Σ ⊢ e[x := e'] => v
-------------------------------
Σ ⊢ e e' => v

```

Is there any point to having higher-order functions?
```
let when =
  λ f: 'a -> 'b.
  λ a: option 'a.
    rec bb.
      match a with
      | None -> None fby bb
      | Some a -> f a
```

```
let match_opt =
  λ none: 'b.
  λ some: 'a -> 'b.
  λ v: option 'a.
    merge
      (when v.tag = None: none)
      (when v.tag = Some: some v.data)
```

# Extension: buffers
```
e ::= …
  | buf.new nat v e
  | buf.get e e'

τ ::= …
  | buf τ

--
buf ¬stable


    v: τ
Γ ⊢ e: τ
--
Γ ⊢ buf.new n v e: τ

Γ ⊢ e:  buf τ
Γ ⊢ e': nat
--
Γ ⊢ buf.get e e': τ


v ::= buf v [v]


drop i Σ ⊢ e => vᵢ for i ∈ [0, n)
--
Σ ⊢ buf.new n v e => buf v [v₀…vₙ]

Σ ⊢ e => buf v vs
Σ ⊢ e' => i
i < |vs|
--
Σ ⊢ buf.get e e' => vsₙ

Σ ⊢ e => buf v vs
Σ ⊢ e' => i
i >= |vs|
--
Σ ⊢ buf.get e e' => v
```


# Extension: clocks, no resets

## Examples
```
let count_by(x: int): int =
  rec c. (0 fby c) + x

let count_sem(ck: bool): bool =
  (count_by when ck)(1 when ck)
   ==
  (count_by(if ck then 1 else 0) when ck)

==>

λck: bool.
  ((λx. rec c₁. (0 fby c₁) + x) when ck)(1 when ck)
   ==
  (rec c₂. (0 fby c₂) + (if ck then 1 else 0)) when ck)

==>

  (λx: int on ck.
    unwrap ck (rec c₁. (0 fby c₁) + x))
    (1 when ck)

  ==>

  unwrap ck
    (rec c₁. (0 fby c₁) + 1)

  ==>
    (rec c₁.
      if ck
      then (0 fby c₁) + 1
      else ⊥ fby c₁)
    when ck

  =or=>
    (rec c₁. 0 fby (if ck then (c₁ + 1) else c₁))
    when ck

  =or=>
    (rec c₁. 0 fby (c₁ when ck) + 1)
    when ck


(0 fby (x when k)) = (rec m. 0 fby (if k then x else m)) when k


```

## Rules

```
v ::= … | ⊥

κ := x | true | false | current κ

τ ::= …
  | τ on κ

e ::= …
  | whenₖ e
  | unwrapₖ e // "e by p" in λ*
  | currentₖ e
  | mergeₖ e e'
```

```
Γ ⊢ e: τ
--
Γ ⊢ whenₖ e: τ on k


unwrapₖ Γ ⊢ e: τ
--
Γ ⊢ unwrapₖ e: τ on κ


Γ ⊢ e: τ on k
--
Γ ⊢ currentₖ e: τ on (current k)

Γ ⊢ e:  τ on k
Γ ⊢ e': τ
--
Γ ⊢ mergeₖ e e': τ
```

```
Σ ⊢       k => true
Σ ⊢       e => v
--
Σ ⊢ whenₖ e => v

Σ ⊢       k => false
--
Σ ⊢ whenₖ e => ⊥


unwrapₖ Σ ⊢         e => v
--
Σ ⊢ unwrapₖ e => v


--
. ⊢ currentₖ e => ⊥

σ :: Σ ⊢          k => true
σ :: Σ ⊢          e => v
--
σ :: Σ ⊢ currentₖ e => v

σ :: Σ ⊢          k => false
     Σ ⊢ currentₖ e => v
--
σ :: Σ ⊢ currentₖ e => v


Σ ⊢           k => true
Σ ⊢        e    => v
--
Σ ⊢ mergeₖ e e' => v

Σ ⊢          k  => false
Σ ⊢          e' => v
--
Σ ⊢ mergeₖ e e' => v
```

## Rewrite rules

when, unwrap, current, merge, app, λ, fby, rec

### when
```
whenₖ₁ (whenₖ₂ e) ~ whenₖ₂ (whenₖ₁ e)

whenₖ₁ (unwrapₖ₂ e) ?

whenₖ (currentₖ e) = e

whenₖ (mergeₖ e e') = e

whenₖ (f e) /= (whenₖ f) (whenₖ e)
  let fₖ = whenₖ f in
  let eₖ = whenₖ e in
  unwrapₖ (fₖ eₖ)

whenₖ (λx. e) = ?

whenₖ (v fby e) /= v fby (whenₖ e)

whenₖ (rec x. e) /= rec x. ...
```
