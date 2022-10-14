import MyNat.Definition
import MyNat.Addition -- add_succ
import MyNat.Multiplication -- mul_succ
import AdvancedAdditionWorld.Level9 -- succ_ne_zero
import Mathlib.Tactic.LeftRight
namespace MyNat
open MyNat

/-!
# Advanced Multiplication World

## Level 2: `eq_zero_or_eq_zero_of_mul_eq_zero`

A variant on the previous level.

## Theorem
If `ab = 0`, then at least one of `a` or `b` is equal to zero.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : MyNat) (h : a * b = 0) :
  a = 0 ∨ b = 0 := by
  cases a with
  | zero =>
    left
    rfl
  | succ a' =>
    cases b with
    | zero =>
      right
      rfl
    | succ b' =>
      exfalso
      rw [mul_succ] at h
      rw [add_succ] at h
      exact succ_ne_zero _ h
/-!

Next up [Level 3](./Level3.lean.md)
-/
