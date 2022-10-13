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
  · rintro ⟨HP, HQ | HR⟩
    left; constructor <;> assumption
    right; constructor <;> assumption
  . rintro (⟨HP, HQ⟩ | ⟨HP, HR⟩)
    constructor; assumption; left; assumption
    constructor; assumption; right; assumption
/-!


## Pro tip

Did you spot the `import Mathlib.Tactic.LeftRight`? What do you think it does?

You can make Mathlib available to your Lean package by adding the following
to your `lakefile.lean`:
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56b19bdec560037016e326795d0feaa23b402c20"
```
This specifies a precise version of mathlib4 by commit Id.

-/

/-!
Next up [Level 9](./Level9.lean.md)
-/
