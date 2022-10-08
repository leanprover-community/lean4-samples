import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced proposition world.

## Level 3: and_trans.

## Lemma
If `P`, `Q` and `R` are true/false statements, then `P ∧ Q` and
`Q ∧ R` together imply `P ∧ R`.
-/
lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq
  intro hqr
  exact ⟨hpq.left, hqr.right⟩

/-!
Next up [Level 4](./Level4.lean.md)
-/