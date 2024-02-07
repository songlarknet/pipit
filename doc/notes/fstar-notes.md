# FStar things


```
FSTAR_NL_DISABLE="--z3smtopt '(set-option :smt.arith.nl false)'"
FSTAR_ARITH_UNBOX="--smtencoding.l_arith_repr native --smtencoding.elim_box true"
```

## Reducing flakiness


Query stats:
```
#push-options "--query_stats"
```

Quantifier instantiations are cumulative, so put #restart-solver before definition to get an accurate number.

Seems to help:
```
#push-options --fuel 1 --ifuel 1
```

### Quake

To check 5 times:
```
#push-options "--quake 5/k"
```

## Getting stats

```

#push-options "--log_queries"
#restart-solver

```

Then run z3 on generated smt2 file:
```
z3 queries-MODULE.smt2 smt.qi.profile=true > sample_qiprofile
grep quantifier_instances sample_qiprofile | sort -k 4 -n
```

## Hiding definitions
```
[@@"opaque_to_smt"]
let unbounded (f: nat → int) = forall (m: nat). exists (n:nat). abs (f n) > m


let instantiate_unbounded (f:nat → int { unbounded f }) (m:nat)
  : Lemma (exists (n:nat). abs (f n) > m)
  = reveal_opaque (`%unbounded) (unbounded f)

```

Triggers
```
let trigger (x:int) = True

let unbounded_alt (f: nat → int) = forall (m: nat). {:pattern (trigger m)} (exists (n:nat). abs (f n) > m)

```

## Manually inverting

To remove the ifuel restrictions for a specific type:
```
   allow_inversion <TYPE>;
```
But not recommended for types with unbounded recursion

## Norm
```
[@@"opaque_to_smt"]
let some_definition (x:nat) = x + 1

let use_norm_spec (x:nat) =
  let y = some_definition x in
  norm_spec [delta] (some_definition x);
  assert (y == x + 1)
```

## Debugging
```
#push-options "--tactic_trace_d 3"
```

Maybe useful:
```
--trace_error --error_contexts true
```

# Resources

* https://github.com/FStarLang/FStar/wiki/Profiling-Z3-queries#interpreting-the-results
* https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html#understanding-how-f-uses-z3

