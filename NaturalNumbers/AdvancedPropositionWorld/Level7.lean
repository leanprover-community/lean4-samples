import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
/-!
# Advanced Proposition World

## Level 7: `or_symm`

Proving that `(P ∨ Q) ⟹ (Q ∨ P)` involves an element of danger. `intro h` is the obvious start. But
now, even though the goal is an `∨` statement, both `left` and `right` put you in a situation with
an impossible goal. Fortunately, after `intro h` you can do `cases h with`. Then something new
happens: because there are two ways to prove `P ∨ Q` (namely, proving `P` or proving `Q`), the
`cases` tactic turns one goal into two, one for each case. Each branch is easy to solve
using the `left` and `right` tactics we used in [Level 6](./Level6.lean.md).

## Lemma
If `P` and `Q` are true/false statements, then `P ∨ Q ⟹ Q ∨ P`.
-/
lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

/-!


Next up [Level 8](./Level8.lean.md).
-/