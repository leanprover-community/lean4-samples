import MyNat.Addition
import MyNat.Multiplication
import AdditionWorld.Level1 -- zero_add
import AdditionWorld.Level5 -- one_eq_succ_zero, succ_eq_add_one
namespace MyNat
open MyNat

/-!
# Multiplication World

## Level 3: `one_mul`

These proofs from addition world might be useful here:

* `one_eq_succ_zero : 1 = succ 0`
* `succ_eq_add_one a : succ a = a + 1`

We just proved `mul_one`, now let's prove `one_mul`. Then we will have proved, in fancy terms, that
1 is a "left and right identity" for multiplication (just like we showed that 0 is a left and right
identity for addition with `add_zero` and `zero_add`).

## Lemma

For any natural number `m`, we have `1 * m = m`.
-/
lemma one_mul (m : MyNat) : 1 * m = m := by
  induction m with
  | zero =>
    rw [zero_is_0]
    rw [mul_zero]
  | succ m ih =>
    rw [mul_succ]
    rw [ih]
    rw [succ_eq_add_one]

/-!
Next up is [Multiplication Level 4](./Level4.lean.md).
-/