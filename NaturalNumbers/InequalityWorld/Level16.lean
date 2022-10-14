import MyNat.Definition
import MyNat.Addition -- add_zero
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import AdditionWorld.Level2 -- add_assoc
import AdditionWorld.Level3 -- succ_add
import InequalityWorld.Level5 -- le_trans
import InequalityWorld.Level6 -- le_antisymm
import InequalityWorld.Level10 -- le_succ_self
import AdvancedAdditionWorld.Level13 -- ne_succ_self
namespace MyNat
open MyNat
/-!

# Inequality world.

## Level 16: equivalence of two definitions of `<`

Now let's go the other way.

## Lemma : lt_aux₂
For all naturals `a` and `b`, `succ a ≤ b  ⟹ a ≤ b ∧ ¬ (b ≤ a)`.
-/
lemma lt_aux₂ (a b : MyNat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := by
  intro h
  constructor
  {
    apply le_trans a (succ a) b
    exact le_succ_self a
    exact h
  }
  {
    intro nh
    apply ne_succ_self a
    apply le_antisymm a (succ a)
    exact le_succ_self a
    exact le_trans (succ a) b a h nh
  }

/-!
Now for the payoff.

Next up [Level 17](./Level17.lean.md)
-/
