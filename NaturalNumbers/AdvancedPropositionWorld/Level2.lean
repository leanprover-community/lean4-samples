import MyNat.Definition
namespace MyNat
open MyNat
/-!


# Advanced proposition world.

## Level 2: the `cases` tactic.

If `P ∧ Q` is in the goal, then we can make progress with `constructor`. But what if `P ∧ Q` is a
hypothesis?

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is, symmetry of the "and" relation. The
obvious first move is

`intro h`

because the goal is an implication and this tactic is guaranteed to make progress. Now `h : P ∧ Q`
is a hypothesis, and we can extract the parts of this `And.intro` using the [`cases` tactic](../Tactics/cases.lean.md)

`cases h with`

This will give us two hypotheses `p` and `q` proving `P` and `Q` respectively.  So we hold onto
these, the goal is now `⊢ Q ∧ P` which we can split using the `constructor` tactic, then we can
easily pick off the two sub-goals `⊢ Q` and  `⊢ P` using `q` and `p` respectively.

## Lemma
If `P` and `Q` are true/false statements, then `P ∧ Q ⟹ Q ∧ P`.
-/
lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro p q =>
    constructor
    exact q
    exact p

/-!


Next up [Level 3](./Level3.lean.md)
-/