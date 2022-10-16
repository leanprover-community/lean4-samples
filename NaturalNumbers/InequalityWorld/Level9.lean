import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import AdvancedAdditionWorld.Level11 -- add_right_eq_zero
import Mathlib.Tactic.LeftRight
import InequalityWorld.Level4 -- zero_le
import InequalityWorld.Level8 -- succ_le_succ
namespace MyNat
open MyNat
/-!
# Inequality World

## Level 9: `le_total`

## Lemma: `le_total`
For all naturals `a` and `b`, either `a ≤ b` or `b ≤ a`.
-/
theorem le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  revert a
  induction b with
  | zero =>
    intro a
    right
    exact zero_le a
  | succ d hd =>
    intro a
    cases a with
    | zero =>
      left
      exact zero_le _
    | succ a =>
      have h2 := hd a
      cases h2 with
      | inl h =>
        left
        exact succ_le_succ a d h
      | inr h =>
        right
        exact succ_le_succ d a h

/-!
See the [revert tactic](../Tactics/revert.lean.md)

Note in the above proof that `exact succ_le_succ a d h`
is just shorthand for:
`
apply succ_le_succ a d
exact h
`

Another collectible: the naturals are a linear order.

-- BUGBUG: collectibles
-- instance : linear_order MyNat := by structure_helper

Next up [Level 10](./Level10.lean.md).
-/
