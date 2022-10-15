import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Basic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import PropositionWorld.Level8 -- not_iff_imp_false
/-!
# Advanced Proposition World

You already know enough to embark on advanced addition world. But here are just a couple
more things.

## Level 9: `exfalso` and proof by contradiction

It's certainly true that `P ∧ (¬ P) ⟹ Q` for any propositions `P`
and `Q`, because the left hand side of the implication is false. But how do
we prove that `False` implies any proposition `Q`? A cheap way of doing it in
Lean is using the [`exfalso` tactic](../Tactics/exfalso.lean.md), which changes any goal at all to `False`.
You might think this is a step backwards, but if you have a hypothesis `h : ¬ P`
then after `rw not_iff_imp_false at h` you can `apply h` to make progress.

## Lemma
If `P` and `Q` are true/false statements, then `(P ∧ (¬ P)) ⟹ Q`.
-/
lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro h
  cases h with
  | intro p np =>
    exfalso
    apply np
    assumption


/-!
## Pro tip.

`¬ P` is actually `P → False` *by definition* and since `np: ¬ P` is a hypothesis,
`apply q` changes `⊢ False` to `⊢ P`.  Neat trick.  We started with `⊢ Q`, but
could not prove it so we jumped to `False` so we could use `np: ¬ P` to get to
the desired goal `⊢ P`.

Next up [Level 10](./Level10.lean.md).
-/