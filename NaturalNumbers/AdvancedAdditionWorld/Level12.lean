import MyNat.Definition
import MyNat.Addition
import AdditionWorld.Level5 -- succ_eq_add_one
namespace MyNat
open MyNat

/-!

# Advanced Addition World

## Level 12: `add_one_eq_succ`

We have

  * `succ_eq_add_one (n : MyNat) : succ n = n + 1`

but sometimes the other way is also convenient.

## Theorem
For any natural number `d`, we have ` d+1 = succ d`.
-/
theorem add_one_eq_succ (d : MyNat) : d + 1 = succ d := by
  rw [succ_eq_add_one]

/-!
Next up [Level 13](./Level13.lean.md).
-/