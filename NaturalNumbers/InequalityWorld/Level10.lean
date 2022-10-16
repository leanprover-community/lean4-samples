import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
namespace MyNat
open MyNat
/-!

# Inequality World

## Level 10: `le_succ_self`

Another simple one.

## Lemma: `le_succ_self`
For all naturals `a`, `a ≤ succ a.`
-/
lemma le_succ_self (a : MyNat) : a ≤ succ a := by
  use 1

/-!
Next up [Level 11](./Level11.lean.md).
-/
