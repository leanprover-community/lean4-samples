import MyNat.Definition
namespace MyNat
open MyNat
/-!


# Advanced proposition world.

## Level 2: the `cases` tactic.

If `P ∧ Q` is in the goal, then we can make progress with `constructor`.
But what if `P ∧ Q` is a hypothesis?

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
symmetry of the "and" relation. The obvious first move is

`intro h`

because the goal is an implication and this tactic is guaranteed
to make progress. Now `h : P ∧ Q` is a hypothesis, and
we can split the `Q ∧ P` goal using `constructor`

`constructor`

This will give us two sub-goals `⊢ P` and `⊢ Q` which we
can complete using `exact` reaching into the `left` and `right`
fields of `h`.

## Lemma
If `P` and `Q` are true/false statements, then `P ∧ Q ⟹ Q ∧ P`.
-/
lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  exact h.right
  exact h.left

/-!

Here's the lean 3 version:
```lean
lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with p q,
  split,
  exact q,
  exact p,
end
```


Next up [Level 3](./Level3.lean.md)
-/