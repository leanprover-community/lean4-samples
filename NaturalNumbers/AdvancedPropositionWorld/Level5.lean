import MyNat.Definition
namespace MyNat
open MyNat
/-!

# Advanced proposition world.

## Level 5: `iff_trans` easter eggs.

Let's try `iff_trans` again. Try proving it in other ways.

### A trick.

Instead of using `cases` on `h : P ↔ Q` you can just access the proofs of `P → Q` and `Q → P`
directly with `h.mp` and `h.mpr`.

## Lemma
If `P`, `Q` and `R` are true/false statements, then `P ↔ Q` and `Q ↔ R` together imply `P ↔ R`.
-/
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros hpq hqr
  constructor
  intro p
  apply hqr.mp
  apply hpq.mp
  assumption
  intro r
  apply hpq.mpr
  apply hqr.mpr
  assumption

/-!

Here's the lean 3 version:
```lean
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hpq hqr,
  split,
  intro p,
  apply hqr.1,
  apply hpq.1,
  assumption,
  intro r,
  apply hpq.2,
  apply hqr.2,
  assumption,
end
```

### Another trick

Instead of using `cases` on `h : P ↔ Q`, you can just `rw h`, and this will change all `P`s to `Q`s
in the goal. You can use this to create a much shorter proof. Note that
this is an argument for *not* running the `cases` tactic on an iff statement;
you cannot rewrite one-way implications, but you can rewrite two-way implications.

-/
lemma iff_trans₂ (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros hpq hqr
  rw [hpq]
  rw [hqr]

/-!


Next up [Level 6](./Level6.lean.md)
-/