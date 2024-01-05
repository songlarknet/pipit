# Missing proofs
## High

High-priority proofs related to translation correctness

### Pipit.Exp.Causality (base)
prove lemma-bigstep-total

### Pipit.System.Exp (trans)
no translation for free vars: just treat them as oracles

### Pipit.System.Exp.Properties (trans)
translation is an abstraction (big)

### Pipit.Prim.Table (base, easy)
simple context proofs


## Mid

Medium-priority proofs related to preservation of checks

### Pipit.Exp.Checked.Base (checks)
bless proofs

### Pipit.Sugar.Check (checks)
induction is sound (big)

### Pipit.System.Ind (checks)
induction is sound, checks are preserved

## Low

Low-priority proofs: mainly just annoying

### Pipit.Exp.Checked.Compound (checks, sugar)
compounds preserve check

### Pipit.Exp.Binding.Property (base)
FLAKY
