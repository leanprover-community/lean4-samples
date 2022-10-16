import MyNat.Power
import MultiplicationWorld.Level2 -- mul_one
namespace MyNat
open MyNat

/-!
# Power World

## Level 4: `one_pow`

## Lemma
For all naturals `m`, `1 ^ m = 1`.
-/
lemma one_pow (m : MyNat) : (1 : MyNat) ^ m = 1 := by
  induction m with
  | zero =>
    rw [zero_is_0]
    rw [pow_zero]
  | succ m ih =>
    rw [pow_succ]
    rw [ih]
    rw [mul_one]


/-!
Next up [Level 5](./Level5.lean.md).
-/