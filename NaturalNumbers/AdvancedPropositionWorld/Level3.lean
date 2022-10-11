import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced proposition world.

## Level 3: and_trans.

With this proof we can use the `have` tactic to introduce a new hypotheses
that can then allow `assumption` to finish the proof.

## Lemma
If `P`, `Q` and `R` are true/false statements, then `P ∧ Q` and
`Q ∧ R` together imply `P ∧ R`.
-/
lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq
  intro hqr
  constructor
  have p := hpq.left
  assumption
  have r := hqr.right
  assumption

/-!

Here's the lean 3 version:
```lean
lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=
begin
  intro hpq,
  intro hqr,
  cases hpq with p q,
  cases hqr with q' r,
  split,
  assumption,
  assumption,
end
```
Next up [Level 4](./Level4.lean.md)
-/