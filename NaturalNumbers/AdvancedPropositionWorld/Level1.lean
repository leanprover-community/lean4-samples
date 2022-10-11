import Mathlib.Tactic.Cases
import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced Proposition world

## Level 1: the `split` tactic.

The logical symbol `∧` means "and". If `P` and `Q` are propositions, then
`P ∧ Q` is the proposition "`P` and `Q`". If your *goal* is `P ∧ Q` then
you can make progress with the `constructor` tactic, which turns one goal `⊢ P ∧ Q`
into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a `constructor`,
you can finish off the two new sub-goals with the `exact` tactic.

## Lemma
If `P` and `Q` are true, then `P ∧ Q` is true.
-/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  exact p
  exact q
/-!

Here's the lean 3 version:

```lean
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
begin
  split,
  exact p,
  exact q,
end
```

Next up [Level 2](./Level2.lean.md)
-/