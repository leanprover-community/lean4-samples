import MyNat.Definition
namespace MyNat
open MyNat
/-!
# Proposition World

## Level 6: `(P → (Q → R)) → ((P → Q) → (P → R))`

You can solve this level completely just using `intro`, `apply` and `exact`,
but if you want to argue forwards instead of backwards then don't forget
that you can do things like `have j : Q → R := f p` if `f : P → (Q → R)`
and `p : P`. I recommend that you start with `intro f` rather than `intro p`
because even though the goal starts `P → ...`, the brackets mean that
the goal is not the statement that `P` implies anything, it's the statement that
`P ⟹ (Q ⟹ R)` implies something. In fact I'd recommend that you started
with `intro f h p`, which introduces three variables at once.
You then find that your your goal is `⊢ R`. If you try `have j : Q → R := f p`
now then you can `apply j`. Alternatively you can `apply (f p)` directly.
What happens if you just try `apply f`? Can you figure out what just happened? This is a little
`apply` easter egg. Why is it mathematically valid?

## Lemma
If `P` and `Q` and `R` are true/false statements, then
\\((P⟹(Q⟹ R))⟹((P⟹ Q)⟹(P⟹ R))\\).
-/
example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  intro f
  intro h
  intro p
  have j : Q → R := f p
  apply j
  apply h
  exact p

/-!
Next up [Level 7](./Level7.lean.md).
-/