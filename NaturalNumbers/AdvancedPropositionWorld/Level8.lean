import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Basic
import Mathlib.Tactic.CasesM
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
/-!
# Advanced proposition world.

## Level 8: `and_or_distrib_left`

We know that `x(y+z)=xy+xz` for numbers, and this
is called distributivity of multiplication over addition.
The same is true for `∧` and `∨` -- in fact `∧` distributes
over `∨` and `∨` distributes over `∧`. Let's prove one of these.

## Lemma
If `P`. `Q` and `R` are true/false statements, then
`P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R).`
-/
-- lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
--   constructor
--   intro h
--   ???

/-!

Here's the lean 3 version:
```lean
lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  split,
  intro h,
  cases h with hp hqr,
  cases hqr with q r,
  left, split, assumption, assumption,
  right, split, assumption, assumption,
  intro h,
  cases h with hpq hpr,
  cases hpq with p q,
  split, assumption,
  left, assumption,
  cases hpr with hp hr,
  split, assumption,
  right, assumption,
end
```

## Pro tip

Did you spot the `import Mathlib.Tactic.Cases`? What do you think it does?

You can make Mathlib available to your Lean package by adding the following
to your `lakefile.lean`:
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56b19bdec560037016e326795d0feaa23b402c20"
```
This specifies a precise version of mathlib4 by commit Id.

-/

/-!
Next up [Level 9](./Level9.lean.md)
-/