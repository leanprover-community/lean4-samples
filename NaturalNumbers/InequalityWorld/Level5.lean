import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level2 -- add_assoc
namespace MyNat
open MyNat
/-!

# Inequality world.

## Level 5: `le_trans`

Another straightforward one.

## Lemma
≤ is transitive. In other words, if `a ≤ b` and `b ≤ c` then `a ≤ c`.
-/
theorem le_trans (a b c : MyNat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | _ d hd =>
    cases hbc with
    | _ e he =>
      use (d + e)
      rw [←add_assoc]
      rw [←hd]
      assumption

/-!
This proved that the natural numbers are a preorder.
-/
-- BUGBUG collectibles
-- instance : preorder MyNat := by structure_helper

/-!
Next up [Level 6](./Level6.lean.md)
-/
