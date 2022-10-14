import MyNat.Definition
import MyNat.Addition -- add_zero
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level2 -- add_assoc
import AdditionWorld.Level3 -- succ_add
import InequalityWorld.Level2 -- le_refl
namespace MyNat
open MyNat
/-

# Inequality world.

## Level 15: introducing `<`

To get the remaining collectibles in this world, we need to
give a definition of `<`. By default, the definition of `a < b`
in Lean, once `≤` is defined, is this:

`a < b := a ≤ b ∧ ¬ (b ≤ a)`

But a much more usable definition would be this:

`a < b := succ a ≤ b`

Let's prove that these two definitions are the same
-/

/- Lemma :
For all naturals `a` and `b`,
``a ≤ b ∧ ¬(b ≤ a) ⟹ succ a ≤ b.``
-/
lemma lt_aux₁ (a b : MyNat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := by
  intro h
  cases h with
  | _ h1 h2 =>
    cases h1 with
    | _ c hc =>
      cases c with
      | zero =>
        exfalso
        rw [zero_is_0, add_zero] at hc
        apply h2
        rw [hc]
      | succ d =>
        use d
        rw [hc]
        rw [add_succ]
        rw [succ_add]

/-!
Next up [Level 16](./Level16.lean.md)
-/
