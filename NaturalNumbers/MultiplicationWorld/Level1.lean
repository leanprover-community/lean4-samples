import MyNat.Addition
import MyNat.Multiplication
namespace MyNat
open MyNat

/-!

## Level 1: `zero_mul`

## Lemma

For all natural numbers `m`, we have ` 0 * m = 0. `
-/
lemma zero_mul (m : MyNat) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [zero_is_0]
    rw [mul_zero]
  | succ m ih =>
    rw [mul_succ]
    rw [ih]
    rw [add_zero]

/-!
Next up is [Multiplication Level 2](./Level2.lean.md).
-/