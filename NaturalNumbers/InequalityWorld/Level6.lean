import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level2 -- add_assoc
import AdvancedAdditionWorld.Level8 -- eq_zero_of_add_right_eq_self
import AdvancedAdditionWorld.Level11 -- add_right_eq_zero
namespace MyNat
open MyNat
/-!

# Inequality world.

## Level 6: `le_antisymm`

In Advanced Addition World you proved

`eq_zero_of_add_right_eq_self (a b : MyNat) : a + b = a → b = 0`.

This might be useful in this level.

Another tip: if you want to create a new hypothesis, you can use the `have` tactic.
For example, if you have a hypothesis `hd : a + (c + d) = a` and you want
a hypothesis `h : c + d = 0` then you can write

`have h := eq_zero_of_add_right_eq_self hd`

## Lemma : le_antisymm
`≤` is antisymmetric. In other words, if `a ≤ b` and `b ≤ a` then `a = b`.
-/
theorem le_antisymm (a b : MyNat) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | _ c hc =>
    cases hba with
    | _ d hd =>
      rw [hc, add_assoc] at hd
      have hd := hd.symm
      have h := eq_zero_of_add_right_eq_self hd
      have h2 := add_right_eq_zero h
      rw [h2] at hc
      rw [hc]
      exact add_zero a

/-!
This proved that the natural numbers are a partial order!
-/
-- BUGBUG : collectibles
-- instance : partial_order MyNat := by structure_helper

/-!
Next up [Level 7](./Level7.lean.md)
-/
