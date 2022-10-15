import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level1 -- zero_add
namespace MyNat
open MyNat
/-!

# Inequality World

## Level 4: `zero_le`

Another easy one.

## Lemma : zero_le
For all naturals `a`, `0 ≤ a`.
-/
lemma zero_le (a : MyNat) : 0 ≤ a := by
  use a
  rw [zero_add]

/-!
Next up [Level 5](./Level5.lean.md).
-/
