import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Basic
import Std.Tactic.RCases
/-!
# Advanced proposition world.

## Level 8: `and_or_distrib_left`

We know that `x(y+z)=xy+xz` for numbers, and this is called distributivity of multiplication over
addition. The same is true for `∧` and `∨` -- in fact `∧` distributes over `∨` and `∨` distributes
over `∧`. Let's prove one of these.

Some new tactics are handy here, the `rintro` tactic is a combination of the `intros` tactic with
`rcases` to allow for destructuring patterns while introducing variables. For example,
`rintro ⟨HP, HQ | HR⟩` below matches the subgoal `P ∧ (Q ∨ R)` and introduces the new hypothesis
`HP : P` and breaks the Or `Q ∨ R` into two left and right sub-goals each with
hypothesis `HQ : Q` and `HR : R`.

Notice here that you can use a semi-colon to separate multiple tactics on the same line. Another
trick shown below is the `<;>`. We could have written `left; constructor; assumption; assumption`
since the `constructor` produces two sub-goals we need 2 `assumption` tactics to close those, or you
can just write `<;> assumption` which runs `assumption` on both sub-goals.

## Lemma
If `P`. `Q` and `R` are true/false statements, then
`P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R).`
-/
lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  { rintro ⟨HP, HQ | HR⟩
    left; constructor <;> assumption
    right; constructor <;> assumption
  }
  { rintro (⟨HP, HQ⟩ | ⟨HP, HR⟩)
    constructor; assumption; left; assumption
    constructor; assumption; right; assumption
  }
/-!


## Pro tip

Notice here we have used curly braces to group the answers to each of the two sub-goals produced by
the `constructor` tactic.  But you if you don't like curly braces you can also use dots like this:

-/
lemma and_or_distrib_left₂ (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  . rintro ⟨HP, HQ | HR⟩
    left; constructor <;> assumption
    right; constructor <;> assumption
  . rintro (⟨HP, HQ⟩ | ⟨HP, HR⟩)
    constructor; assumption; left; assumption
    constructor; assumption; right; assumption
/-!
Where the definition of the dot is:

> Given a goal state [g1, g2, ... gn], . tacs is a tactic which first changes the goal state to [g1],
then runs tacs. If the resulting goal state is not [], throw an error.
Then restore the remaining goals [g2, ..., gn].


Next up [Level 9](./Level9.lean.md)
-/
