import PowerWorld.Level1
import MyNat.Multiplication -- mul_zero
namespace MyNat
open MyNat

/-!

# Power World

## Level 2: `zero_pow_succ`

## Lemma
For all naturals `m`, `0 ^ (succ m) = 0`.
-/
lemma zero_pow_succ (m : MyNat) : (0 : MyNat) ^ (succ m) = 0 := by
  rw [pow_succ]
  rw [mul_zero]


/-!
Next up [Level 3](./Level3.lean.md)
-/