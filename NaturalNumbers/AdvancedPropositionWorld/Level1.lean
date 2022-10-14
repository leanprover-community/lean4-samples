import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced Proposition world

## Level 1: the `constructor` tactic.

The logical symbol `∧` means "and". If `P` and `Q` are propositions, then `P ∧ Q` is the proposition
"`P` and `Q`". If your *goal* is `P ∧ Q` then you can make progress with the [`constructor` tactic](../Tactics/constructor.lean.md).,
which turns one goal `⊢ P ∧ Q` into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a
`constructor`, you can finish off the two new sub-goals with the `exact` tactic since both `p` and
`q` provide exactly what we need.  You could also use the `assumption` tactic.

## Lemma
If `P` and `Q` are true, then `P ∧ Q` is true.
-/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  exact p
  exact q
/-!


Next up [Level 2](./Level2.lean.md)
-/