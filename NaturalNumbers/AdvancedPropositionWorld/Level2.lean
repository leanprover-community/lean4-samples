import MyNat.Definition
namespace MyNat
open MyNat
/-!


# Advanced proposition world.

## Level 2: the `cases` tactic.

If `P ∧ Q` is in the goal, then we can make progress with `split`.
But what if `P ∧ Q` is a hypothesis? In this case, the `cases` tactic will enable
us to extract proofs of `P` and `Q` from this hypothesis.

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
symmetry of the "and" relation. The obvious first move is

`intro h`

because the goal is an implication and this tactic is guaranteed
to make progress. Now `h : P ∧ Q` is a hypothesis, and

`cases h with p q`

will change `h`, the proof of `P ∧ Q`, into two proofs `p : P`
and `q : Q`. From there, `split` and `exact` will get you home.

## Lemma
If `P` and `Q` are true/false statements, then `P ∧ Q ⟹ Q ∧ P`.
-/
lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨ h.right, h.left ⟩



/-!
Next up [Level 3](./Level3.lean.md)
-/