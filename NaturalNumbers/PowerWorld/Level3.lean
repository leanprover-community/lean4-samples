import MyNat.Power
import AdditionWorld.Level5 -- one_eq_succ_zero
import MultiplicationWorld.Level3 -- one_mul
namespace MyNat
open MyNat

/-!

# Power World

## Level 3: `pow_one`

## Lemma
For all naturals `a`, `a ^ 1 = a`.
-/
lemma pow_one (a : MyNat) : a ^ (1 : MyNat) = a := by
  rw [one_eq_succ_zero]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]


/-!
Next up [Level 4](./Level4.lean.md).
-/