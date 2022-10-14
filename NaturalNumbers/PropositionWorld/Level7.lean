import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Function world.

## Level 7: `(P → Q) → ((Q → R) → (P → R))`

If you start with `intro hpq` and then `intro hqr`
the dust will clear a bit and the level will look like this:
```
P Q R : Prop,
hpq : P → Q,
hqr : Q → R
⊢ P → R
```
So this level is really about showing transitivity of `⟹`,
if you like that sort of language.

## Lemma : imp_trans

From `P ⟹ Q` and `Q ⟹ R` we can deduce `P ⟹ R`.
-/
lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  intros hpq hqr
  intro p
  apply hqr
  apply hpq
  assumption

/-!
Here we finish this proof with a new tactic `assumption` instead of `exact p`.
The `assumption` tactic tries to solve the goal using a
hypothesis of compatible type.  Since we have the hypothesis named `p` it finds
it and completes the proof.

Next up [Level 8](./Level8.lean.md)
-/