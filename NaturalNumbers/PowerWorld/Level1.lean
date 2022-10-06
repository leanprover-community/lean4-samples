import MyNat.Power
namespace MyNat
open MyNat

/-!
## Level 1: `zero_pow_zero`

Given the lemma `pow_zero` which says `m ^ 0 = 1`
you can now prove zero to the power of zero is also one.

## Lemma
`0 ^ 0 = 1`.
-/
lemma zero_pow_zero : (0 : MyNat) ^ (0 : MyNat) = 1 := by
  rw [pow_zero]

/-!
That was easy!  Next up [Level 2](./Level2.lean.md)
-/