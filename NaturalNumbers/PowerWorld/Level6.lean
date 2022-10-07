import MyNat.Power
import MultiplicationWorld.Level2 -- mul_one
import MultiplicationWorld.Level9 -- simp additions
namespace MyNat
open MyNat

/-!

# Power World

## Level 6: `mul_pow`

Here we use the `attribute [simp]` additions we made in
[level 9 of Multiplication World](../MultiplicationWorld/Level9.lean.md)
so that the `simp` tactic can simplify expressions involving `*`.

## Lemma
For all naturals `a`, `b`, `n`, we have `(ab) ^ n = a ^ nb ^ n`.
-/
lemma mul_pow (a b n : MyNat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    rw [zero_is_0]
    repeat rw [pow_zero]
    rw [mul_one]
  | succ n ih =>
    repeat rw [pow_succ]
    rw [ih]
    simp


/-!
Next up [Level 7](./Level7.lean.md)
-/