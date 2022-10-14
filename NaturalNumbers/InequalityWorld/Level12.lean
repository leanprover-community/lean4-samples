import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level6 -- add_right_comm
import AdvancedAdditionWorld.Level1 --  succ_inj
namespace MyNat
open MyNat
/-!

# Inequality world.

## Level 12: `le_of_succ_le_succ`

## Lemma
For all naturals `a` and `b`, `succ a ≤ succ b ⟹ a ≤ b.`
-/
theorem le_of_succ_le_succ (a b : MyNat) : succ a ≤ succ b → a ≤ b := by
  intro h
  cases h with
  | _ c hc =>
    use c
    apply succ_inj
    rw [hc]
    exact succ_add a c

/-!
Next up [Level 13](./Level13.lean.md)
-/
