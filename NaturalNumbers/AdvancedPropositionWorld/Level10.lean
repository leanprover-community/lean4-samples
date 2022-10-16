import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced Proposition World

## Level 10: the law of the excluded middle

We proved earlier that `(P → Q) → (¬ Q → ¬ P)`. The converse,
that `(¬ Q → ¬ P) → (P → Q)` is certainly true, but trying to prove
it using what we've learnt so far is impossible (because it is not provable in
constructive logic). For example, after

```
intro h
intro p
repeat rw [not_iff_imp_false] at h
```

below you are left with
```
P Q : Prop
h : (Q → False) → P → False
p : P
⊢ Q
```

The tools you have are not sufficient to continue. But you can just prove this, and any other basic
lemmas of this form like `¬ ¬ P → P`, using the [`by_cases` tactic](../Tactics/by_cases.lean.md). Here we start with the usual
`intro` to turn the implication into hypotheses `h : ¬ Q → ¬ P` and `p : P` which leaves with the
goal of `⊢ Q`.  But how can you prove `Q` using these hypotheses?  You can use this tactic:

`by_cases q : Q`

This creates two sub-goals `pos` and `neg` with the first one assuming Q is true - which can easily
satisfy the goal! - and the second one assuming Q is false. But how can `h: ¬Q → ¬P`, `p: P`, `q: ¬Q`
prove the goal `⊢ Q`? Well if you apply `q` to the hypothesis `h` you end up with the conclusion
`¬ P`, but then you have a contradiction in your hypotheses saying `P` and `¬ P` which the
[`contradiction` tactic](../Tactics/contradiction.lean.md) can take care of.

The `contradiction` tactic closes the main goal if its hypotheses
are "trivially contradictory".

## Lemma
If `P` and `Q` are true/false statements, then `(¬ Q ⟹ ¬ P) ⟹ (P ⟹ Q)`.
-/
lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  intro h
  intro p
  by_cases q : Q
  exact q
  have np := h q
  contradiction
/-!

OK that's enough logic -- now perhaps it's time to go on to [Advanced Addition World](../AdvancedAdditionWorld.lean.md)!

## Pro tip

In fact the [tactic `tauto!`](../Tactics/tauto.lean.md) just kills this goal (and many other logic goals) immediately.

Each of these can now be proved using `intro`, `apply`, `exact` and `exfalso`.
Remember though that in these simple logic cases, high-powered logic
tactics like `tauto!` will just prove everything.


-/
