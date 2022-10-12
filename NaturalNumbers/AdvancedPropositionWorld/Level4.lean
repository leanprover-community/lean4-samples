import MyNat.Definition
namespace MyNat
open MyNat
/-!

# Advanced proposition world.

## Level 4: `iff_trans`.

The mathematical statement `P ↔ Q` is equivalent to `(P ⟹ Q) ∧ (Q ⟹ P)`. The `cases`
and `split` tactics work on hypotheses and goals (respectively) of the form `P ↔ Q`.

> If you need to write an `↔` arrow in Visual Studio Code you can do so by typing `\iff`.
See the "Lean 4: Show All Abbreviations" command.

After an initial `intro h` you can type `cases h with hpq hqp` to break `h : P ↔ Q` into its constituent parts.

## Lemma
If `P`, `Q` and `R` are true/false statements, then `P ↔ Q` and `Q ↔ R` together imply `P ↔ R`.
-/
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq
  intro hqr
  constructor
  cases hpq with
  | intro pq qp =>
    cases hqr with
    | intro qr rq =>
      intro p
      apply qr
      apply pq
      exact p
  cases hpq with
  | intro pq qp =>
    cases hqr with
    | intro qr rq =>
      intro r
      apply qp
      apply rq
      exact r
/-!


Here's the lean 3 version:
```lean
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro hpq,
  intro hqr,
  cases hpq with hpq hqp,
  cases hqr with hqr hrq,
  split,
  cc,cc,
end
```
Next up [Level 5](./Level5.lean.md)
-/