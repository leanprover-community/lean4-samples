import MyNat.Definition
import MyNat.Addition -- add_zero
import MyNat.Inequality -- le_iff_exists_add
import Mathlib.Tactic.Use -- use tactic
import InequalityWorld.Level15 -- lt_aux₁
import InequalityWorld.Level16 -- lt_aux₂
import AdvancedAdditionWorld.Level13 -- ne_succ_self
namespace MyNat
open MyNat
/-!

# Inequality World

## Level 17: definition of `<`

OK so we are going to *define* `a < b` by `a ≤ b ∧ ¬ (b ≤ a)`,
and given `lt_aux_one a b` and `lt_aux_two a b` it should now just
be a few lines to prove `a < b ↔ succ a ≤ b`.

## Lemma : `lt_iff_succ_le`
For all naturals `a` and `b`, `a<b ↔ succ a ≤ b`.
-/
lemma lt_iff_succ_le (a b : MyNat) : a < b ↔ succ a ≤ b := by
  constructor
  exact lt_aux₁ a b
  exact lt_aux₂ a b

/-!
Sadly that is the end of all our nicely documented levels in this tutorial!

Interested in playing levels involving other kinds of mathematics?
Look <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/WHATS_NEXT.md"
  target="blank">here</a> for more ideas about what to do next.

Interested in learning more? Join us on the
<a href="https://leanprover.zulipchat.com/" target="blank">Zulip Lean chat</a>
and ask questions in the `#new members` stream. Real names preferred. Be nice.
-/

/-!
If you want to see a whole bunch of great examples see [Level 18](./Level18.lean.md).
-/
