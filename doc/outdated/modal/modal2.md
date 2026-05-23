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

# Extension: clocks, no resets

Options

```
unwrapₖ Γ ⊢ e: τ
--
Γ ⊢ unwrapₖ e: τ on κ
```

- complicated? global
- relation to `when` unclear
+ seems expressive enough

```
Γ ⊢ e: (τ₁ → τ₂) on k
Γ ⊢ e': τ₁ on k
--
Γ ⊢ e @ck e': τ₂ on k
```

+ simple, local
+ matches applicative functor
- does not support fby, rec?

```
Γ        ⊢ e₁: τ₁ on k
Γ, x: τ₁ ⊢ e₂: τ₂ on k
--
Γ ⊢ let when x = e₁ in e₂: τ₂ on k
```

+ simple, local
+ matches let-box
- interferes with previous modality: `rec x: int on k. let when x': ●int = x in (0 fby x') + 1`
  but `rec x: int on k. (0 fby (let when x': int = x in x')) + 1`

## Examples
```
let count_by(x: int): int =
  rec c. (0 fby c) + x

let count_sem(ck: bool): bool =
  (let when cby = count_by when ck in
   (cby 1) when ck)
   ==
  (count_by @ (if ck then 1 else 0)) when ck

==>

unwrap:
  (unwrap (count_by 1))

clocked-apps:
  (count_by when ck) @ck (1 when ck)

  ==>

  ((λx. rec c₁. (0 fby c₁) + x) when ck) @ck (1 when ck)

  ==>

  (λx: int on ck.
    (rec c₁. (0 fby c₁) + x) when ck
  ) @ (1 when ck)

  ==>
    (rec c₁. (0 fby c₁) +_ck (1 when ck)) when ck

  ==>
    (rec_ck c₁: int on ck.
      (0 fby_ck c₁) +_ck (1 when ck))

let-when:

  let when cby = (λx. rec c₁. (0 fby c₁) + x) when ck in
  (cby @ 1) when ck

  ==>

  (λx: int on ck.
    let when x':  int = x  in
    rec c₁: int on ck.
      let when c₁': int = c₁ in
      ((0 fby c₁') + x') when ck) @ (1 when ck)

  ==>
    let when x':  int = 1 when ck in
    rec c₁: int on ck.
      let when c₁': ● int = c₁ in
      ((0 fby c₁') + x') when ck



λck: bool.
  ((λx. rec c₁. (0 fby c₁) + x) when ck) @ck (1 when ck)
   ==
  (rec c₂. (0 fby c₂) + (if ck then 1 else 0))) when ck

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
