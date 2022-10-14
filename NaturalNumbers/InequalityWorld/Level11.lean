import MyNat.Definition
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level6 -- add_right_comm
namespace MyNat
open MyNat
/-

# Inequality world.

## Level 11: `add_le_add_right`

If you're faced with a goal of the form `forall t, ...`, then the next
line is "so let `t` be arbitrary". The way to do this in Lean is `intro t`.

## Lemma
For all naturals `a` and `b`, `a ≤ b` implies that for all naturals `t`,
`a+t ≤ b+t`.
-/
theorem add_le_add_right {a b : MyNat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h
  cases h with
  | _ c hc =>
    intro t
    use c
    rw [hc]
    rw [add_right_comm]

/-!
Next up [Level 12](./Level12.lean.md)
-/
