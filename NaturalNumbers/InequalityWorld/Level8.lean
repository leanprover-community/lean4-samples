import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdvancedAdditionWorld.Level11 -- add_right_eq_zero
namespace MyNat
open MyNat
/-!

# Inequality World

## Level 8: `succ_le_succ`

Another straightforward one.

## Lemma : succ_le_succ
For all naturals `a` and `b`, if `a ≤ b`, then `succ a ≤ succ b`.
-/
lemma succ_le_succ (a b : MyNat) (h : a ≤ b) : succ a ≤ succ b := by
  cases h with
  | _ c hc =>
    use c
    rw [hc]
    rw [succ_add]


/-!
Next up [Level 9](./Level9.lean.md).
-/
