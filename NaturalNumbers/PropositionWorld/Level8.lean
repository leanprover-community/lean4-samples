import MyNat.Definition
namespace MyNat
open MyNat

/-!
# Proposition World

## Level 8 : `(P → Q) → (¬ Q → ¬ P)`

There is a false proposition `False`, with no proof. It is easy to check that `¬ Q` is equivalent to
`Q ⟹ False`, and in this tutorial we call this

`not_iff_imp_false (P : Prop) : ¬ P ↔ (P → False)`

which we can prove here using the `simp` tactic:
-/
theorem not_iff_imp_false (P : Prop) : ¬ P ↔ (P → false) :=
  by simp
/-!
So you can start the proof of the contrapositive below with

`repeat rw [not_iff_imp_false]`

to get rid of the two occurrences of `¬`, and I'm sure you can take it from there. At some point
your goal might be to prove `False`. At that point I guess you must be proving something by
contradiction. Or are you?

## Lemma : contrapositive
If `P` and `Q` are propositions, and `P⟹ Q`, then
`¬ Q⟹ ¬ P`.
-/
lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  repeat rw [not_iff_imp_false]
  intro f
  intro h
  intro p
  apply h
  apply f
  exact p

/-!
## Technical note

All of that rewriting you did with `rw` in addition world was rewriting hypothesis of the form
`h : X = Y`, but you can also `rw [h]` if `h : P ↔ Q` (because propositional extensionality says
that if `P ⟺ Q` then `P = Q`, and mathematicians use this whether or not they notice.)
-/

/-!
Next up [Level 9](./Level9.lean.md).
-/