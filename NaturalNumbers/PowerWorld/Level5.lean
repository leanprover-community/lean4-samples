import MyNat.Power
import MyNat.Addition -- add_zero
import MultiplicationWorld.Level2 -- mul_one
import MultiplicationWorld.Level5 -- mul_assoc
namespace MyNat
open MyNat

/-!
# Power World

## Level 5: `pow_add`

## Lemma
For all naturals `a`, `m`, `n`, we have `a^(m + n) = a ^ m * a ^ n`.
-/
lemma pow_add (a m n : MyNat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    rw [zero_is_0]
    rw [add_zero]
    rw [pow_zero]
    rw [mul_one]
  | succ n ih =>
    rw [add_succ]
    rw [pow_succ]
    rw [pow_succ]
    rw [ih]
    rw [mul_assoc]

/-!
Remember you can combine all the `rw` rules into one with
`rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]` but we have
broken it out here so you can more easily see all the intermediate
goal states.

Next up [Level 6](./Level6.lean.md).
-/