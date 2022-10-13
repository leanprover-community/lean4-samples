import Mathlib.Tactic.LeftRight
/-!
# Advanced proposition world.

## Level 6: Or, and the `left` and `right` tactics.

`P ∨ Q` means "`P` or `Q`". So to prove it, you need to choose one of `P` or `Q`, and prove that
one. If `⊢ P ∨ Q` is your goal, then `left` changes this goal to `⊢ P`, and `right` changes it to `⊢ Q`.
Note that you can take a wrong turn here. Let's start with trying to prove `Q ⟹ (P ∨ Q)`. After
the `intro`, one of `left` and `right` leads to an impossible goal, the other to an easy finish.

## Lemma
If `P` and `Q` are true/false statements, then `Q ⟹(P ∨ Q).`
-/
example (P Q : Prop) : Q → (P ∨ Q) := by
  intro q
  right
  assumption

/-!
## Details

The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`.
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.


## Pro Tip!


Did you spot the `import Mathlib.Tactic.LeftRight`? What do you think it does?

You can make Mathlib available to your Lean package by adding the following
to your `lakefile.lean`:
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "56b19bdec560037016e326795d0feaa23b402c20"
```
This specifies a precise version of mathlib4 by commit Id.


Next up [Level 7](./Level7.lean.md)
-/