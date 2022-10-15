import MyNat.Definition
import MultiplicationWorld.Level1 -- zero_mul
import AdvancedMultiplicationWorld.Level2 -- eq_zero_or_eq_zero_of_mul_eq_zero
import Mathlib.Tactic.LeftRight
namespace MyNat
open MyNat

/-!
# Advanced Multiplication World

## Level 3: `mul_eq_zero_iff`

Now you have `eq_zero_or_eq_zero_of_mul_eq_zero` this is pretty straightforward.

## Theorem
`ab = 0` if and only if at least one of `a` or `b` is equal to zero.
-/
theorem mul_eq_zero_iff (a b : MyNat): a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  {
     intro h
     exact eq_zero_or_eq_zero_of_mul_eq_zero a b h
  }
  {
    intro hab
    cases hab with
    | inl ha =>
      rw [ha]
      rw [zero_mul]
    | inr hb =>
      rw [hb]
      rw [mul_zero]
  }

/-!

Next up [Level 4](./Level4.lean.md).
-/
