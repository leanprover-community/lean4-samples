import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level4 -- add_comm
import AdvancedAdditionWorld.Level10 -- add_left_eq_zero
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 11: `add_right_eq_zero`

We just proved `add_left_eq_zero (a b : MyNat) : a + b = 0 → b = 0`.
Hopefully `add_right_eq_zero` shouldn't be too hard now.

## Lemma
If `a` and `b` are natural numbers such that if `a + b = 0` then `a = 0`.
-/
lemma add_right_eq_zero {a b : MyNat} : a + b = 0 → a = 0 := by
  intro h
  rw [add_comm] at h
  exact add_left_eq_zero h


/-!
Next up [Level 12](./Level12.lean.md).
-/