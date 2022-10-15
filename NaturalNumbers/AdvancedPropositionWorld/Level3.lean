import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Advanced Proposition World

## Level 3: and_trans

With this proof we can use the first `cases` tactic to extract hypotheses `p : P` and `q : Q` from
`hpq : P ∧ Q` and then we can use another `cases` tactic to extract hypotheses `q' : Q` and `r : R` from
`hpr : Q ∧ R` then we can split the resulting goal `⊢ P ∧ R` using `constructor` and easily pick off the
resulting sub-goals `⊢ P` and `⊢ R` using our given hypotheses.

## Lemma
If `P`, `Q` and `R` are true/false statements, then `P ∧ Q` and
`Q ∧ R` together imply `P ∧ R`.
-/
lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq
  intro hqr
  cases hpq with
  | intro p q =>
    cases hqr with
    | intro q' r =>
      constructor
      assumption
      assumption

/-!

Next up [Level 4](./Level4.lean.md).
-/